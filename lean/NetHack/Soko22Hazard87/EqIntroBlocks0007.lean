import NetHack.Soko22Hazard87.EqIntroBlocks0006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro1750 (p : Pattern) (selected : d3188 p = 0) : d58479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3183 q = 0) : d58474 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3183, d58474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3183, d58474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1749 q selected
  have h2 (q : Pattern) (selected : d3184 q = 0) : d58475 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3184, d58475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3184, d58475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3185 q = 0) : d58476 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3185, d58476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3185, d58476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3186 q = 0) : d58477 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3186, d58477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3186, d58477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3187 q = 0) : d58478 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3187, d58478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3187, d58478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3188 q = 0) : d58479 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3188, d58479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3188, d58479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1751 (p : Pattern) (selected : d3201 p = 0) : d58492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d790 q = 0) : d52467 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d790, d52467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro325 q selected
  have h2 (q : Pattern) (selected : d791 q = 0) : d52468 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d791, d52468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d800 q = 0) : d52477 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro325 q selected
    | true =>
      simp only [d800, d52477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro328 q selected
  have h4 (q : Pattern) (selected : d801 q = 0) : d52478 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d801, d52478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d802 q = 0) : d52479 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d802, d52479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d938 q = 0) : d52557 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d52557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro350 q selected
    | true =>
      simp only [d938, d52557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro358 q selected
  have h7 (q : Pattern) (selected : d3190 q = 0) : d58481 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3190, d58481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3190, d58481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3191 q = 0) : d58482 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3191, d58482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3191, d58482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3192 q = 0) : d58483 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3192, d58483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3192, d58483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d958 q = 0) : d52577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d958, d52577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d958, d52577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro361 q selected
  have h11 (q : Pattern) (selected : d3193 q = 0) : d58484 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3193, d58484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3193, d58484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3194 q = 0) : d58485 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3194, d58485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3194, d58485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3195 q = 0) : d58486 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3195, d58486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3195, d58486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3196 q = 0) : d58487 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3196, d58487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3196, d58487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1059 q = 0) : d52644 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1059, d52644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1059, d52644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro379 q selected
  have h16 (q : Pattern) (selected : d3197 q = 0) : d58488 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3197, d58488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3197, d58488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3198 q = 0) : d58489 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3198, d58489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3198, d58489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3199 q = 0) : d58490 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3199, d58490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3199, d58490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3200 q = 0) : d58491 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3200, d58491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3200, d58491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3201 q = 0) : d58492 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3201, d58492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3201, d58492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro1752 (p : Pattern) (selected : d3207 p = 0) : d58498 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3202 q = 0) : d58493 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3202, d58493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3202, d58493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1751 q selected
  have h2 (q : Pattern) (selected : d3203 q = 0) : d58494 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3203, d58494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3203, d58494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3204 q = 0) : d58495 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3204, d58495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3204, d58495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3205 q = 0) : d58496 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3205, d58496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3205, d58496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3206 q = 0) : d58497 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3206, d58497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3206, d58497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3207 q = 0) : d58498 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3207, d58498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3207, d58498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1753 (p : Pattern) (selected : d3221 p = 0) : d58512 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1169 q = 0) : d52750 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1169, d52750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro397 q selected
  have h2 (q : Pattern) (selected : d1170 q = 0) : d52751 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1170, d52751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1179 q = 0) : d52760 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro397 q selected
    | true =>
      simp only [d1179, d52760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro400 q selected
  have h4 (q : Pattern) (selected : d1180 q = 0) : d52761 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1180, d52761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1181 q = 0) : d52762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1181, d52762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1349 q = 0) : d52837 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d52837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro426 q selected
    | true =>
      simp only [d1349, d52837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro434 q selected
  have h7 (q : Pattern) (selected : d3210 q = 0) : d58501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3210, d58501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3210, d58501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3211 q = 0) : d58502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3211, d58502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3211, d58502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3212 q = 0) : d58503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3212, d58503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3212, d58503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1369 q = 0) : d52857 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1369, d52857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1369, d52857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro437 q selected
  have h11 (q : Pattern) (selected : d3213 q = 0) : d58504 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3213, d58504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3213, d58504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3214 q = 0) : d58505 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3214, d58505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3214, d58505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3215 q = 0) : d58506 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3215, d58506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3215, d58506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3216 q = 0) : d58507 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3216, d58507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3216, d58507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1493 q = 0) : d52938 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1493, d52938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1493, d52938, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro455 q selected
  have h16 (q : Pattern) (selected : d3217 q = 0) : d58508 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3217, d58508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3217, d58508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3218 q = 0) : d58509 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3218, d58509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3218, d58509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3219 q = 0) : d58510 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3219, d58510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3219, d58510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3220 q = 0) : d58511 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3220, d58511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3220, d58511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3221 q = 0) : d58512 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3221, d58512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3221, d58512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro1754 (p : Pattern) (selected : d3227 p = 0) : d58518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3222 q = 0) : d58513 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3222, d58513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3222, d58513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1753 q selected
  have h2 (q : Pattern) (selected : d3223 q = 0) : d58514 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3223, d58514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3223, d58514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3224 q = 0) : d58515 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3224, d58515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3224, d58515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3225 q = 0) : d58516 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3225, d58516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3225, d58516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3226 q = 0) : d58517 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3226, d58517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3226, d58517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3227 q = 0) : d58518 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3227, d58518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3227, d58518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1755 (p : Pattern) (selected : d3242 p = 0) : d58533 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1630 q = 0) : d53071 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1630, d53071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro479 q selected
  have h2 (q : Pattern) (selected : d1631 q = 0) : d53072 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1631, d53072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1640 q = 0) : d53081 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro479 q selected
    | true =>
      simp only [d1640, d53081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro482 q selected
  have h4 (q : Pattern) (selected : d1641 q = 0) : d53082 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1641, d53082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1642 q = 0) : d53083 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1642, d53083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1826 q = 0) : d53152 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d53152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro512 q selected
    | true =>
      simp only [d1826, d53152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro520 q selected
  have h7 (q : Pattern) (selected : d3231 q = 0) : d58522 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3231, d58522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3231, d58522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3232 q = 0) : d58523 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3232, d58523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3232, d58523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3233 q = 0) : d58524 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3233, d58524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3233, d58524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d1846 q = 0) : d53172 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1846, d53172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1846, d53172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro523 q selected
  have h11 (q : Pattern) (selected : d3234 q = 0) : d58525 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3234, d58525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3234, d58525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3235 q = 0) : d58526 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3235, d58526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3235, d58526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3236 q = 0) : d58527 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3236, d58527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3236, d58527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3237 q = 0) : d58528 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3237, d58528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3237, d58528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d1970 q = 0) : d53253 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1970, d53253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1970, d53253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro541 q selected
  have h16 (q : Pattern) (selected : d3238 q = 0) : d58529 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3238, d58529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3238, d58529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3239 q = 0) : d58530 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3239, d58530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3239, d58530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3240 q = 0) : d58531 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3240, d58531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3240, d58531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3241 q = 0) : d58532 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3241, d58532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3241, d58532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3242 q = 0) : d58533 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3242, d58533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3242, d58533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro1756 (p : Pattern) (selected : d3248 p = 0) : d58539 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3243 q = 0) : d58534 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3243, d58534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3243, d58534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1755 q selected
  have h2 (q : Pattern) (selected : d3244 q = 0) : d58535 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3244, d58535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3244, d58535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3245 q = 0) : d58536 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3245, d58536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3245, d58536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3246 q = 0) : d58537 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3246, d58537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3246, d58537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3247 q = 0) : d58538 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3247, d58538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3247, d58538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3248 q = 0) : d58539 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3248, d58539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3248, d58539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1757 (p : Pattern) (selected : d3264 p = 0) : d58555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2113 q = 0) : d53392 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2113, d53392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro568 q selected
  have h2 (q : Pattern) (selected : d2114 q = 0) : d53393 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2114, d53393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2123 q = 0) : d53402 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro568 q selected
    | true =>
      simp only [d2123, d53402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro571 q selected
  have h4 (q : Pattern) (selected : d2124 q = 0) : d53403 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2124, d53403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2125 q = 0) : d53404 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2125, d53404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2304 q = 0) : d53469 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d53469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro602 q selected
    | true =>
      simp only [d2304, d53469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro610 q selected
  have h7 (q : Pattern) (selected : d3253 q = 0) : d58544 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3253, d58544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3253, d58544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3254 q = 0) : d58545 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3254, d58545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3254, d58545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d3255 q = 0) : d58546 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3255, d58546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3255, d58546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2324 q = 0) : d53489 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2324, d53489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2324, d53489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro613 q selected
  have h11 (q : Pattern) (selected : d3256 q = 0) : d58547 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3256, d58547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3256, d58547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d3257 q = 0) : d58548 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3257, d58548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3257, d58548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d3258 q = 0) : d58549 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3258, d58549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3258, d58549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d3259 q = 0) : d58550 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3259, d58550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3259, d58550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2448 q = 0) : d53570 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2448, d53570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2448, d53570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro631 q selected
  have h16 (q : Pattern) (selected : d3260 q = 0) : d58551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3260, d58551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3260, d58551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d3261 q = 0) : d58552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3261, d58552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d3261, d58552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d3262 q = 0) : d58553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3262, d58553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d3262, d58553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d3263 q = 0) : d58554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3263, d58554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d3263, d58554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d3264 q = 0) : d58555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3264, d58555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3264, d58555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
  exact h20 p selected
theorem eqIntro1758 (p : Pattern) (selected : d3270 p = 0) : d58561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3265 q = 0) : d58556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3265, d58556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3265, d58556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1757 q selected
  have h2 (q : Pattern) (selected : d3266 q = 0) : d58557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3266, d58557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3266, d58557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3267 q = 0) : d58558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3267, d58558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3267, d58558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3268 q = 0) : d58559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3268, d58559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3268, d58559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3269 q = 0) : d58560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3269, d58560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3269, d58560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3270 q = 0) : d58561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3270, d58561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3270, d58561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1759 (p : Pattern) (selected : d3276 p = 0) : d58567 p = 1 := by
  have h0 (q : Pattern) (selected : d3189 q = 0) : d58480 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3189, d58480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1748 q selected
    | true =>
      simp only [d3189, d58480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1750 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d3208 q = 0) : d58499 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3208, d58499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3208, d58499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1752 q selected
  have h3 (q : Pattern) (selected : d3209 q = 0) : d58500 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3209, d58500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3209, d58500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3228 q = 0) : d58519 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3228, d58519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3228, d58519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1754 q selected
  have h5 (q : Pattern) (selected : d3229 q = 0) : d58520 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3229, d58520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3229, d58520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3230 q = 0) : d58521 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3230, d58521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3230, d58521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3249 q = 0) : d58540 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3249, d58540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3249, d58540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1756 q selected
  have h8 (q : Pattern) (selected : d3250 q = 0) : d58541 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3250, d58541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3250, d58541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3251 q = 0) : d58542 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3251, d58542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3251, d58542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3252 q = 0) : d58543 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3252, d58543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3252, d58543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3271 q = 0) : d58562 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3271, d58562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3271, d58562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1758 q selected
  have h12 (q : Pattern) (selected : d3272 q = 0) : d58563 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3272, d58563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3272, d58563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3273 q = 0) : d58564 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3273, d58564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3273, d58564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3274 q = 0) : d58565 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3274, d58565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3274, d58565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3275 q = 0) : d58566 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3275, d58566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3275, d58566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3276 q = 0) : d58567 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3276, d58567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3276, d58567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1760 (p : Pattern) (selected : d3282 p = 0) : d58573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3277 q = 0) : d58568 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3277, d58568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1759 q selected
    | true =>
      simp only [d3277, d58568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3278 q = 0) : d58569 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3278, d58569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3278, d58569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3279 q = 0) : d58570 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3279, d58570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3279, d58570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3280 q = 0) : d58571 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3280, d58571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3280, d58571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3281 q = 0) : d58572 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3281, d58572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3281, d58572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3282 q = 0) : d58573 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3282, d58573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3282, d58573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1761 (p : Pattern) (selected : d3288 p = 0) : d58579 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3283 q = 0) : d58574 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3283, d58574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1760 q selected
    | true =>
      simp only [d3283, d58574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3284 q = 0) : d58575 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3284, d58575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3284, d58575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3285 q = 0) : d58576 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3285, d58576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3285, d58576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3286 q = 0) : d58577 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3286, d58577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3286, d58577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3287 q = 0) : d58578 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3287, d58578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3287, d58578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3288 q = 0) : d58579 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3288, d58579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3288, d58579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1762 (p : Pattern) (selected : d3294 p = 0) : d58585 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3289 q = 0) : d58580 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3289, d58580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1761 q selected
    | true =>
      simp only [d3289, d58580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3290 q = 0) : d58581 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3290, d58581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3290, d58581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3291 q = 0) : d58582 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3291, d58582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3291, d58582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3292 q = 0) : d58583 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3292, d58583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3292, d58583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3293 q = 0) : d58584 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3293, d58584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3293, d58584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3294 q = 0) : d58585 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3294, d58585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3294, d58585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1763 (p : Pattern) (selected : d3300 p = 0) : d58591 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3295 q = 0) : d58586 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3295, d58586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1762 q selected
    | true =>
      simp only [d3295, d58586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3296 q = 0) : d58587 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3296, d58587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3296, d58587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3297 q = 0) : d58588 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3297, d58588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3297, d58588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3298 q = 0) : d58589 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3298, d58589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3298, d58589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3299 q = 0) : d58590 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3299, d58590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3299, d58590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3300 q = 0) : d58591 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3300, d58591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3300, d58591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1764 (p : Pattern) (selected : d3306 p = 0) : d58597 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3301 q = 0) : d58592 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3301, d58592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1763 q selected
    | true =>
      simp only [d3301, d58592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3302 q = 0) : d58593 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3302, d58593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3302, d58593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3303 q = 0) : d58594 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3303, d58594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3303, d58594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3304 q = 0) : d58595 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3304, d58595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3304, d58595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3305 q = 0) : d58596 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3305, d58596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3305, d58596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3306 q = 0) : d58597 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3306, d58597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3306, d58597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1765 (p : Pattern) (selected : d3312 p = 0) : d58603 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3307 q = 0) : d58598 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3307, d58598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1764 q selected
    | true =>
      simp only [d3307, d58598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3308 q = 0) : d58599 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3308, d58599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3308, d58599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3309 q = 0) : d58600 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3309, d58600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3309, d58600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3310 q = 0) : d58601 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3310, d58601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3310, d58601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3311 q = 0) : d58602 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3311, d58602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3311, d58602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3312 q = 0) : d58603 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3312, d58603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3312, d58603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1766 (p : Pattern) (selected : d3318 p = 0) : d58609 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3313 q = 0) : d58604 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3313, d58604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1765 q selected
    | true =>
      simp only [d3313, d58604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3314 q = 0) : d58605 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3314, d58605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3314, d58605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3315 q = 0) : d58606 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3315, d58606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3315, d58606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3316 q = 0) : d58607 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3316, d58607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3316, d58607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3317 q = 0) : d58608 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3317, d58608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3317, d58608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3318 q = 0) : d58609 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3318, d58609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3318, d58609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1767 (p : Pattern) (selected : d3147 p = 1) : d58614 p = 1 := by
  have h0 (q : Pattern) (selected : d114 q = 1) : d114 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d212 q = 1) : d51647 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d51647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5 q selected
    | true =>
      simp only [d212, d51647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro7 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d3143 q = 1) : d58610 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3143, d58610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3143, d58610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3144 q = 1) : d58611 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3144, d58611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3144, d58611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d3145 q = 1) : d58612 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3145, d58612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3145, d58612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d221 q = 1) : d4350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d221, d4350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d221, d4350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8 q selected
  have h7 (q : Pattern) (selected : d222 q = 1) : d4351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222, d4351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d222, d4351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d223 q = 1) : d4352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223, d4352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d223, d4352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d224 q = 1) : d4353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d224, d4353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d224, d4353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d3146 q = 1) : d58613 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3146, d58613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3146, d58613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d269 q = 1) : d4360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d269, d4360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d269, d4360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro12 q selected
  have h12 (q : Pattern) (selected : d270 q = 1) : d4361 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d270, d4361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d270, d4361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d271 q = 1) : d4362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d271, d4362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d271, d4362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d272 q = 1) : d4363 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d272, d4363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d272, d4363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d273 q = 1) : d4364 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d273, d4364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d273, d4364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d3147 q = 1) : d58614 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3147, d58614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3147, d58614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro1768 (p : Pattern) (selected : d3164 p = 1) : d58624 p = 1 := by
  have h0 (q : Pattern) (selected : d294 q = 1) : d294 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d396 q = 1) : d51664 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d51664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19 q selected
    | true =>
      simp only [d396, d51664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro21 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d3153 q = 1) : d58620 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3153, d58620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3153, d58620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3154 q = 1) : d58621 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3154, d58621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3154, d58621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d3155 q = 1) : d58622 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3155, d58622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3155, d58622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d405 q = 1) : d4386 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d405, d4386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d405, d4386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22 q selected
  have h7 (q : Pattern) (selected : d3156 q = 1) : d4387 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3156, d4387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3156, d4387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d3157 q = 1) : d4388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3157, d4388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3157, d4388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d3158 q = 1) : d4389 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3158, d4389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3158, d4389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d3159 q = 1) : d58623 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3159, d58623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3159, d58623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d457 q = 1) : d4396 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d457, d4396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d457, d4396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro26 q selected
  have h12 (q : Pattern) (selected : d3160 q = 1) : d4397 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3160, d4397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3160, d4397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d3161 q = 1) : d4398 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3161, d4398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3161, d4398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d3162 q = 1) : d4399 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3162, d4399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d3162, d4399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d3163 q = 1) : d4400 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3163, d4400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3163, d4400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d3164 q = 1) : d58624 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3164, d58624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3164, d58624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro1769 (p : Pattern) (selected : d3170 p = 1) : d58630 p = 1 := by
  have h0 (q : Pattern) (selected : d99 q = 1) : d99 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3148 q = 1) : d58615 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3148, d58615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3148, d58615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1767 q selected
  have h3 (q : Pattern) (selected : d3149 q = 1) : d58616 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3149, d58616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3149, d58616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3150 q = 1) : d58617 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3150, d58617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3150, d58617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3151 q = 1) : d58618 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3151, d58618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3151, d58618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3152 q = 1) : d58619 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3152, d58619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3152, d58619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3165 q = 1) : d58625 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3165, d58625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3165, d58625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1768 q selected
  have h8 (q : Pattern) (selected : d3166 q = 1) : d58626 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3166, d58626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3166, d58626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3167 q = 1) : d58627 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3167, d58627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3167, d58627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3168 q = 1) : d58628 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3168, d58628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3168, d58628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3169 q = 1) : d58629 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3169, d58629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3169, d58629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3170 q = 1) : d58630 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3170, d58630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3170, d58630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro1770 (p : Pattern) (selected : d3182 p = 1) : d58635 p = 1 := by
  have h0 (q : Pattern) (selected : d510 q = 1) : d510 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d632 q = 1) : d51689 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d51689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36 q selected
    | true =>
      simp only [d632, d51689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro39 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d3171 q = 1) : d58631 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3171, d58631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3171, d58631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3172 q = 1) : d58632 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3172, d58632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3172, d58632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d3173 q = 1) : d58633 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3173, d58633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3173, d58633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d652 q = 1) : d4423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d652, d4423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d652, d4423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40 q selected
  have h7 (q : Pattern) (selected : d3174 q = 1) : d4424 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3174, d4424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3174, d4424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d3175 q = 1) : d4425 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3175, d4425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3175, d4425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d3176 q = 1) : d4426 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3176, d4426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3176, d4426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d3177 q = 1) : d58634 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3177, d58634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3177, d58634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d726 q = 1) : d4433 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d726, d4433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d726, d4433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro46 q selected
  have h12 (q : Pattern) (selected : d3178 q = 1) : d4434 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3178, d4434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3178, d4434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d3179 q = 1) : d4435 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3179, d4435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3179, d4435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d3180 q = 1) : d4436 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3180, d4436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d3180, d4436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d3181 q = 1) : d4437 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3181, d4437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3181, d4437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d3182 q = 1) : d58635 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3182, d58635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3182, d58635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro1771 (p : Pattern) (selected : d3188 p = 1) : d58641 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3183 q = 1) : d58636 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3183, d58636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3183, d58636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1770 q selected
  have h2 (q : Pattern) (selected : d3184 q = 1) : d58637 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3184, d58637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3184, d58637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3185 q = 1) : d58638 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3185, d58638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3185, d58638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3186 q = 1) : d58639 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3186, d58639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3186, d58639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3187 q = 1) : d58640 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3187, d58640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3187, d58640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3188 q = 1) : d58641 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3188, d58641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3188, d58641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1772 (p : Pattern) (selected : d3201 p = 1) : d58647 p = 1 := by
  have h0 (q : Pattern) (selected : d802 q = 1) : d802 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d938 q = 1) : d51715 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d51715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro60 q selected
    | true =>
      simp only [d938, d51715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro63 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d3190 q = 1) : d58643 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3190, d58643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3190, d58643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3191 q = 1) : d58644 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3191, d58644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3191, d58644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d3192 q = 1) : d58645 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3192, d58645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3192, d58645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d958 q = 1) : d4461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d958, d4461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d958, d4461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro64 q selected
  have h7 (q : Pattern) (selected : d3193 q = 1) : d4462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3193, d4462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3193, d4462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d3194 q = 1) : d4463 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3194, d4463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3194, d4463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d3195 q = 1) : d4464 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3195, d4464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3195, d4464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d3196 q = 1) : d58646 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3196, d58646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3196, d58646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1059 q = 1) : d4471 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1059, d4471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1059, d4471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro72 q selected
  have h12 (q : Pattern) (selected : d3197 q = 1) : d4472 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3197, d4472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3197, d4472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d3198 q = 1) : d4473 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3198, d4473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3198, d4473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d3199 q = 1) : d4474 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3199, d4474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d3199, d4474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d3200 q = 1) : d4475 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3200, d4475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3200, d4475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d3201 q = 1) : d58647 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3201, d58647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3201, d58647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro1773 (p : Pattern) (selected : d3207 p = 1) : d58653 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3202 q = 1) : d58648 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3202, d58648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3202, d58648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1772 q selected
  have h2 (q : Pattern) (selected : d3203 q = 1) : d58649 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3203, d58649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3203, d58649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3204 q = 1) : d58650 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3204, d58650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3204, d58650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3205 q = 1) : d58651 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3205, d58651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3205, d58651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3206 q = 1) : d58652 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3206, d58652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3206, d58652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3207 q = 1) : d58653 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3207, d58653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3207, d58653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1774 (p : Pattern) (selected : d3221 p = 1) : d58660 p = 1 := by
  have h0 (q : Pattern) (selected : d1181 q = 1) : d1181 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1349 q = 1) : d51742 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d51742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro90 q selected
    | true =>
      simp only [d1349, d51742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro93 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d3210 q = 1) : d58656 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3210, d58656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3210, d58656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3211 q = 1) : d58657 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3211, d58657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3211, d58657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d3212 q = 1) : d58658 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3212, d58658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3212, d58658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1369 q = 1) : d4500 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1369, d4500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1369, d4500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro94 q selected
  have h7 (q : Pattern) (selected : d3213 q = 1) : d4501 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3213, d4501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3213, d4501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d3214 q = 1) : d4502 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3214, d4502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3214, d4502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d3215 q = 1) : d4503 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3215, d4503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3215, d4503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d3216 q = 1) : d58659 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3216, d58659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3216, d58659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1493 q = 1) : d4510 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1493, d4510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1493, d4510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro102 q selected
  have h12 (q : Pattern) (selected : d3217 q = 1) : d4511 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3217, d4511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3217, d4511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d3218 q = 1) : d4512 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3218, d4512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3218, d4512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d3219 q = 1) : d4513 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3219, d4513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d3219, d4513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d3220 q = 1) : d4514 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3220, d4514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3220, d4514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d3221 q = 1) : d58660 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3221, d58660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3221, d58660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro1775 (p : Pattern) (selected : d3227 p = 1) : d58666 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3222 q = 1) : d58661 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3222, d58661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3222, d58661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1774 q selected
  have h2 (q : Pattern) (selected : d3223 q = 1) : d58662 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3223, d58662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3223, d58662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3224 q = 1) : d58663 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3224, d58663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3224, d58663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3225 q = 1) : d58664 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3225, d58664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3225, d58664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3226 q = 1) : d58665 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3226, d58665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3226, d58665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3227 q = 1) : d58666 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3227, d58666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3227, d58666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1776 (p : Pattern) (selected : d3242 p = 1) : d58674 p = 1 := by
  have h0 (q : Pattern) (selected : d1642 q = 1) : d1642 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1826 q = 1) : d51770 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d51770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro126 q selected
    | true =>
      simp only [d1826, d51770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro129 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d3231 q = 1) : d58670 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3231, d58670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3231, d58670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3232 q = 1) : d58671 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3232, d58671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3232, d58671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d3233 q = 1) : d58672 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3233, d58672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3233, d58672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1846 q = 1) : d4540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1846, d4540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1846, d4540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro130 q selected
  have h7 (q : Pattern) (selected : d3234 q = 1) : d4541 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3234, d4541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3234, d4541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d3235 q = 1) : d4542 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3235, d4542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3235, d4542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d3236 q = 1) : d4543 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3236, d4543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3236, d4543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d3237 q = 1) : d58673 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3237, d58673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3237, d58673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1970 q = 1) : d4550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1970, d4550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1970, d4550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro138 q selected
  have h12 (q : Pattern) (selected : d3238 q = 1) : d4551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3238, d4551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3238, d4551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d3239 q = 1) : d4552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3239, d4552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3239, d4552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d3240 q = 1) : d4553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3240, d4553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d3240, d4553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d3241 q = 1) : d4554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3241, d4554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3241, d4554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d3242 q = 1) : d58674 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3242, d58674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3242, d58674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro1777 (p : Pattern) (selected : d3248 p = 1) : d58680 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3243 q = 1) : d58675 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3243, d58675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3243, d58675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1776 q selected
  have h2 (q : Pattern) (selected : d3244 q = 1) : d58676 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3244, d58676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3244, d58676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3245 q = 1) : d58677 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3245, d58677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3245, d58677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3246 q = 1) : d58678 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3246, d58678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3246, d58678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3247 q = 1) : d58679 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3247, d58679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3247, d58679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3248 q = 1) : d58680 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3248, d58680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3248, d58680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1778 (p : Pattern) (selected : d3264 p = 1) : d58689 p = 1 := by
  have h0 (q : Pattern) (selected : d2125 q = 1) : d2125 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2304 q = 1) : d51799 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d51799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro163 q selected
    | true =>
      simp only [d2304, d51799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro166 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d3253 q = 1) : d58685 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3253, d58685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3253, d58685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3254 q = 1) : d58686 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3254, d58686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3254, d58686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h5 (q : Pattern) (selected : d3255 q = 1) : d58687 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3255, d58687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3255, d58687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2324 q = 1) : d4581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2324, d4581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2324, d4581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro167 q selected
  have h7 (q : Pattern) (selected : d3256 q = 1) : d4582 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3256, d4582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3256, d4582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d3257 q = 1) : d4583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3257, d4583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3257, d4583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h9 (q : Pattern) (selected : d3258 q = 1) : d4584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3258, d4584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3258, d4584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h10 (q : Pattern) (selected : d3259 q = 1) : d58688 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3259, d58688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3259, d58688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2448 q = 1) : d4591 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2448, d4591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2448, d4591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro175 q selected
  have h12 (q : Pattern) (selected : d3260 q = 1) : d4592 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3260, d4592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d3260, d4592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d3261 q = 1) : d4593 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3261, d4593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d3261, d4593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h14 (q : Pattern) (selected : d3262 q = 1) : d4594 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3262, d4594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d3262, d4594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h15 (q : Pattern) (selected : d3263 q = 1) : d4595 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3263, d4595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d3263, d4595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h16 (q : Pattern) (selected : d3264 q = 1) : d58689 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3264, d58689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3264, d58689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro1779 (p : Pattern) (selected : d3270 p = 1) : d58695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3265 q = 1) : d58690 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3265, d58690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3265, d58690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1778 q selected
  have h2 (q : Pattern) (selected : d3266 q = 1) : d58691 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3266, d58691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3266, d58691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3267 q = 1) : d58692 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3267, d58692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3267, d58692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3268 q = 1) : d58693 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3268, d58693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3268, d58693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3269 q = 1) : d58694 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3269, d58694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3269, d58694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3270 q = 1) : d58695 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3270, d58695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3270, d58695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1780 (p : Pattern) (selected : d3276 p = 1) : d58701 p = 1 := by
  have h0 (q : Pattern) (selected : d3189 q = 1) : d58642 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3189, d58642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1769 q selected
    | true =>
      simp only [d3189, d58642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1771 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3208 q = 1) : d58654 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3208, d58654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3208, d58654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1773 q selected
  have h3 (q : Pattern) (selected : d3209 q = 1) : d58655 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3209, d58655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3209, d58655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3228 q = 1) : d58667 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3228, d58667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3228, d58667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1775 q selected
  have h5 (q : Pattern) (selected : d3229 q = 1) : d58668 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3229, d58668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3229, d58668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3230 q = 1) : d58669 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3230, d58669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3230, d58669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3249 q = 1) : d58681 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3249, d58681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3249, d58681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1777 q selected
  have h8 (q : Pattern) (selected : d3250 q = 1) : d58682 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3250, d58682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3250, d58682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3251 q = 1) : d58683 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3251, d58683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3251, d58683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3252 q = 1) : d58684 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3252, d58684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3252, d58684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3271 q = 1) : d58696 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3271, d58696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3271, d58696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1779 q selected
  have h12 (q : Pattern) (selected : d3272 q = 1) : d58697 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3272, d58697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3272, d58697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3273 q = 1) : d58698 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3273, d58698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3273, d58698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3274 q = 1) : d58699 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3274, d58699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3274, d58699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3275 q = 1) : d58700 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3275, d58700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3275, d58700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3276 q = 1) : d58701 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3276, d58701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3276, d58701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1781 (p : Pattern) (selected : d3282 p = 1) : d58707 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3277 q = 1) : d58702 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3277, d58702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1780 q selected
    | true =>
      simp only [d3277, d58702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3278 q = 1) : d58703 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3278, d58703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3278, d58703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3279 q = 1) : d58704 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3279, d58704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3279, d58704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3280 q = 1) : d58705 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3280, d58705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3280, d58705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3281 q = 1) : d58706 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3281, d58706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3281, d58706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3282 q = 1) : d58707 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3282, d58707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3282, d58707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1782 (p : Pattern) (selected : d3288 p = 1) : d58713 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3283 q = 1) : d58708 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3283, d58708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1781 q selected
    | true =>
      simp only [d3283, d58708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3284 q = 1) : d58709 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3284, d58709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3284, d58709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3285 q = 1) : d58710 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3285, d58710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3285, d58710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3286 q = 1) : d58711 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3286, d58711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3286, d58711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3287 q = 1) : d58712 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3287, d58712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3287, d58712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3288 q = 1) : d58713 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3288, d58713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3288, d58713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1783 (p : Pattern) (selected : d3294 p = 1) : d58719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3289 q = 1) : d58714 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3289, d58714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1782 q selected
    | true =>
      simp only [d3289, d58714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3290 q = 1) : d58715 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3290, d58715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3290, d58715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3291 q = 1) : d58716 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3291, d58716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3291, d58716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3292 q = 1) : d58717 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3292, d58717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3292, d58717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3293 q = 1) : d58718 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3293, d58718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3293, d58718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3294 q = 1) : d58719 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3294, d58719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3294, d58719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1784 (p : Pattern) (selected : d3300 p = 1) : d58725 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3295 q = 1) : d58720 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3295, d58720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1783 q selected
    | true =>
      simp only [d3295, d58720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3296 q = 1) : d58721 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3296, d58721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3296, d58721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3297 q = 1) : d58722 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3297, d58722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3297, d58722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3298 q = 1) : d58723 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3298, d58723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3298, d58723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3299 q = 1) : d58724 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3299, d58724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3299, d58724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3300 q = 1) : d58725 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3300, d58725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3300, d58725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1785 (p : Pattern) (selected : d3306 p = 1) : d58731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3301 q = 1) : d58726 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3301, d58726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1784 q selected
    | true =>
      simp only [d3301, d58726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3302 q = 1) : d58727 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3302, d58727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3302, d58727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3303 q = 1) : d58728 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3303, d58728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3303, d58728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3304 q = 1) : d58729 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3304, d58729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3304, d58729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3305 q = 1) : d58730 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3305, d58730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3305, d58730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3306 q = 1) : d58731 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3306, d58731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3306, d58731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1786 (p : Pattern) (selected : d3312 p = 1) : d58737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3307 q = 1) : d58732 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3307, d58732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1785 q selected
    | true =>
      simp only [d3307, d58732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3308 q = 1) : d58733 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3308, d58733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3308, d58733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3309 q = 1) : d58734 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3309, d58734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3309, d58734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3310 q = 1) : d58735 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3310, d58735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3310, d58735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3311 q = 1) : d58736 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3311, d58736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3311, d58736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3312 q = 1) : d58737 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3312, d58737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3312, d58737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1787 (p : Pattern) (selected : d3318 p = 1) : d58743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3313 q = 1) : d58738 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3313, d58738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1786 q selected
    | true =>
      simp only [d3313, d58738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3314 q = 1) : d58739 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3314, d58739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3314, d58739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3315 q = 1) : d58740 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3315, d58740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3315, d58740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3316 q = 1) : d58741 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3316, d58741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3316, d58741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3317 q = 1) : d58742 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3317, d58742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3317, d58742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3318 q = 1) : d58743 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3318, d58743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3318, d58743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1788 (p : Pattern) (selected : d58755 p = 0) : d59200 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58751 q = 0) : d59196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58751, d59196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d58751, d59196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58752 q = 0) : d59197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58752, d59197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58752, d59197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58753 q = 0) : d59198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58753, d59198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58753, d59198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58754 q = 0) : d59199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58754, d59199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58754, d59199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58755 q = 0) : d59200 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58755, d59200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58755, d59200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1789 (p : Pattern) (selected : d58760 p = 0) : d59205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58751 q = 0) : d59196 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58751, d59196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
    | true =>
      simp only [d58751, d59196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58752 q = 0) : d59197 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58752, d59197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58752, d59197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58753 q = 0) : d59198 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58753, d59198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58753, d59198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58754 q = 0) : d59199 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58754, d59199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58754, d59199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58756 q = 0) : d59201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58756, d59201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d58756, d59201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58757 q = 0) : d59202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58757, d59202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58757, d59202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58758 q = 0) : d59203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58758, d59203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58758, d59203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58759 q = 0) : d59204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58759, d59204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58759, d59204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58760 q = 0) : d59205 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58760, d59205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58760, d59205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1790 (p : Pattern) (selected : d58764 p = 0) : d59209 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58756 q = 0) : d59201 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58756, d59201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
    | true =>
      simp only [d58756, d59201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58757 q = 0) : d59202 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58757, d59202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58757, d59202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58758 q = 0) : d59203 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58758, d59203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58758, d59203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58759 q = 0) : d59204 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58759, d59204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58759, d59204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58764 q = 0) : d59209 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58764, d59209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58764, d59209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1791 (p : Pattern) (selected : d58773 p = 0) : d59218 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58769 q = 0) : d59214 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58769, d59214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro197 q selected
    | true =>
      simp only [d58769, d59214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d58770 q = 0) : d59215 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58770, d59215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58770, d59215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58771 q = 0) : d59216 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58771, d59216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58771, d59216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58772 q = 0) : d59217 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58772, d59217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58772, d59217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58773 q = 0) : d59218 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58773, d59218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58773, d59218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1792 (p : Pattern) (selected : d58778 p = 0) : d59223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58761 q = 0) : d59206 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58761, d59206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1788 q selected
    | true =>
      simp only [d58761, d59206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1789 q selected
  have h2 (q : Pattern) (selected : d58762 q = 0) : d59207 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58762, d59207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58762, d59207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58763 q = 0) : d59208 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58763, d59208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58763, d59208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58765 q = 0) : d59210 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58765, d59210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58765, d59210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1790 q selected
  have h5 (q : Pattern) (selected : d58766 q = 0) : d59211 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58766, d59211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58766, d59211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58767 q = 0) : d59212 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58767, d59212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58767, d59212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58768 q = 0) : d59213 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58768, d59213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58768, d59213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58774 q = 0) : d59219 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58774, d59219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58774, d59219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1791 q selected
  have h9 (q : Pattern) (selected : d58775 q = 0) : d59220 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58775, d59220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58775, d59220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d58776 q = 0) : d59221 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58776, d59221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58776, d59221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d58777 q = 0) : d59222 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58777, d59222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58777, d59222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d58778 q = 0) : d59223 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58778, d59223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d58778, d59223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro1793 (p : Pattern) (selected : d58788 p = 0) : d59233 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58784 q = 0) : d59229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58784, d59229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58784, d59229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d58785 q = 0) : d59230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58785, d59230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58785, d59230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58786 q = 0) : d59231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58786, d59231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58786, d59231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58787 q = 0) : d59232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58787, d59232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58787, d59232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58788 q = 0) : d59233 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58788, d59233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58788, d59233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1794 (p : Pattern) (selected : d58794 p = 0) : d59239 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58784 q = 0) : d59229 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58784, d59229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58784, d59229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro190 q selected
  have h2 (q : Pattern) (selected : d58785 q = 0) : d59230 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58785, d59230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58785, d59230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58786 q = 0) : d59231 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58786, d59231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58786, d59231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58787 q = 0) : d59232 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58787, d59232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58787, d59232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58790 q = 0) : d59235 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58790, d59235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58790, d59235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro192 q selected
  have h6 (q : Pattern) (selected : d58791 q = 0) : d59236 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58791, d59236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58791, d59236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58792 q = 0) : d59237 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58792, d59237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58792, d59237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58793 q = 0) : d59238 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58793, d59238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58793, d59238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58794 q = 0) : d59239 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58794, d59239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58794, d59239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1795 (p : Pattern) (selected : d58806 p = 0) : d59251 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58797 q = 0) : d59242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58797, d59242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58797, d59242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d58798 q = 0) : d59243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58798, d59243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58798, d59243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58799 q = 0) : d59244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58799, d59244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58799, d59244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58800 q = 0) : d59245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58800, d59245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58800, d59245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h5 (q : Pattern) (selected : d58801 q = 0) : d59246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58801, d59246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58801, d59246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58802 q = 0) : d59247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58802, d59247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d58802, d59247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h7 (q : Pattern) (selected : d58803 q = 0) : d59248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58803, d59248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58803, d59248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d58804 q = 0) : d59249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58804, d59249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58804, d59249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58805 q = 0) : d59250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58805, d59250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58805, d59250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58806 q = 0) : d59251 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58806, d59251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58806, d59251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro1796 (p : Pattern) (selected : d58816 p = 0) : d59261 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58797 q = 0) : d59242 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58797, d59242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58797, d59242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro202 q selected
  have h2 (q : Pattern) (selected : d58798 q = 0) : d59243 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58798, d59243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58798, d59243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58799 q = 0) : d59244 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58799, d59244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58799, d59244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58800 q = 0) : d59245 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58800, d59245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58800, d59245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro203 q selected
  have h5 (q : Pattern) (selected : d58801 q = 0) : d59246 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58801, d59246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58801, d59246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58802 q = 0) : d59247 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58802, d59247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro208 q selected
    | true =>
      simp only [d58802, d59247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro213 q selected
  have h7 (q : Pattern) (selected : d58803 q = 0) : d59248 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58803, d59248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58803, d59248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d58804 q = 0) : d59249 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58804, d59249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58804, d59249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58805 q = 0) : d59250 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58805, d59250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58805, d59250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58807 q = 0) : d59252 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58807, d59252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58807, d59252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro215 q selected
  have h11 (q : Pattern) (selected : d58808 q = 0) : d59253 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58808, d59253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58808, d59253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d58809 q = 0) : d59254 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58809, d59254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58809, d59254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d58810 q = 0) : d59255 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58810, d59255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58810, d59255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro216 q selected
  have h14 (q : Pattern) (selected : d58811 q = 0) : d59256 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58811, d59256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d58811, d59256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d58812 q = 0) : d59257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58812, d59257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d58812, d59257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h16 (q : Pattern) (selected : d58813 q = 0) : d59258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58813, d59258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d58813, d59258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d58814 q = 0) : d59259 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58814, d59259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d58814, d59259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d58815 q = 0) : d59260 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58815, d59260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d58815, d59260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d58816 q = 0) : d59261 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58816, d59261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58816, d59261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro1797 (p : Pattern) (selected : d58822 p = 0) : d59267 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58812 q = 0) : d59257 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58812, d59257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro217 q selected
    | true =>
      simp only [d58812, d59257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro218 q selected
  have h2 (q : Pattern) (selected : d58813 q = 0) : d59258 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58813, d59258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58813, d59258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58820 q = 0) : d59265 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58820, d59265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58820, d59265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58821 q = 0) : d59266 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58821, d59266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58821, d59266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58822 q = 0) : d59267 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58822, d59267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58822, d59267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1798 (p : Pattern) (selected : d58831 p = 0) : d59276 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58827 q = 0) : d59272 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58827, d59272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro224 q selected
    | true =>
      simp only [d58827, d59272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro227 q selected
  have h2 (q : Pattern) (selected : d58828 q = 0) : d59273 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58828, d59273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58828, d59273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58829 q = 0) : d59274 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58829, d59274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58829, d59274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58830 q = 0) : d59275 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58830, d59275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58830, d59275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58831 q = 0) : d59276 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58831, d59276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58831, d59276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1799 (p : Pattern) (selected : d58836 p = 0) : d59281 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58789 q = 0) : d59234 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58789, d59234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58789, d59234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1793 q selected
  have h2 (q : Pattern) (selected : d58795 q = 0) : d59240 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58795, d59240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1793 q selected
    | true =>
      simp only [d58795, d59240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1794 q selected
  have h3 (q : Pattern) (selected : d58796 q = 0) : d59241 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58796, d59241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58796, d59241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58817 q = 0) : d59262 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58817, d59262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1795 q selected
    | true =>
      simp only [d58817, d59262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1796 q selected
  have h5 (q : Pattern) (selected : d58818 q = 0) : d59263 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58818, d59263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58818, d59263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58819 q = 0) : d59264 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58819, d59264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58819, d59264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58823 q = 0) : d59268 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58823, d59268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58823, d59268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1797 q selected
  have h8 (q : Pattern) (selected : d58824 q = 0) : d59269 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58824, d59269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d58824, d59269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d58825 q = 0) : d59270 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58825, d59270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58825, d59270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d58826 q = 0) : d59271 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58826, d59271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58826, d59271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d58832 q = 0) : d59277 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58832, d59277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58832, d59277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1798 q selected
  have h12 (q : Pattern) (selected : d58833 q = 0) : d59278 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58833, d59278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58833, d59278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d58834 q = 0) : d59279 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58834, d59279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d58834, d59279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d58835 q = 0) : d59280 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58835, d59280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d58835, d59280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d58836 q = 0) : d59281 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58836, d59281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58836, d59281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1800 (p : Pattern) (selected : d58842 p = 0) : d59287 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58779 q = 0) : d59224 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58779, d59224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58779, d59224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1792 q selected
  have h2 (q : Pattern) (selected : d58780 q = 0) : d59225 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58780, d59225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58780, d59225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58781 q = 0) : d59226 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58781, d59226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58781, d59226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58782 q = 0) : d59227 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58782, d59227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58782, d59227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58783 q = 0) : d59228 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58783, d59228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58783, d59228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58837 q = 0) : d59282 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58837, d59282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58837, d59282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1799 q selected
  have h7 (q : Pattern) (selected : d58838 q = 0) : d59283 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58838, d59283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58838, d59283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58839 q = 0) : d59284 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58839, d59284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58839, d59284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58840 q = 0) : d59285 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58840, d59285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58840, d59285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58841 q = 0) : d59286 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58841, d59286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58841, d59286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d58842 q = 0) : d59287 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58842, d59287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58842, d59287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro1801 (p : Pattern) (selected : d58847 p = 0) : d59292 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58843 q = 0) : d59288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58843, d59288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58843, d59288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d58844 q = 0) : d59289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58844, d59289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58844, d59289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58845 q = 0) : d59290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58845, d59290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58845, d59290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58846 q = 0) : d59291 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58846, d59291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58846, d59291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58847 q = 0) : d59292 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58847, d59292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58847, d59292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1802 (p : Pattern) (selected : d58853 p = 0) : d59298 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58843 q = 0) : d59288 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58843, d59288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58843, d59288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro266 q selected
  have h2 (q : Pattern) (selected : d58844 q = 0) : d59289 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58844, d59289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58844, d59289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58845 q = 0) : d59290 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58845, d59290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58845, d59290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58846 q = 0) : d59291 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58846, d59291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58846, d59291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58849 q = 0) : d59294 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58849, d59294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58849, d59294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro269 q selected
  have h6 (q : Pattern) (selected : d58850 q = 0) : d59295 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58850, d59295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58850, d59295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58851 q = 0) : d59296 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58851, d59296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58851, d59296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58852 q = 0) : d59297 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58852, d59297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58852, d59297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58853 q = 0) : d59298 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58853, d59298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58853, d59298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1803 (p : Pattern) (selected : d58865 p = 0) : d59310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58856 q = 0) : d59301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58856, d59301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58856, d59301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d58857 q = 0) : d59302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58857, d59302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58857, d59302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58858 q = 0) : d59303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58858, d59303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58858, d59303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58859 q = 0) : d59304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58859, d59304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58859, d59304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro274 q selected
  have h5 (q : Pattern) (selected : d58860 q = 0) : d59305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58860, d59305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58860, d59305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58861 q = 0) : d59306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58861, d59306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d58861, d59306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h7 (q : Pattern) (selected : d58862 q = 0) : d59307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58862, d59307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58862, d59307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d58863 q = 0) : d59308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58863, d59308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58863, d59308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58864 q = 0) : d59309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58864, d59309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58864, d59309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58865 q = 0) : d59310 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58865, d59310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58865, d59310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro1804 (p : Pattern) (selected : d58875 p = 0) : d59320 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58856 q = 0) : d59301 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58856, d59301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58856, d59301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro272 q selected
  have h2 (q : Pattern) (selected : d58857 q = 0) : d59302 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58857, d59302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58857, d59302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58858 q = 0) : d59303 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58858, d59303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58858, d59303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58859 q = 0) : d59304 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58859, d59304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58859, d59304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro274 q selected
  have h5 (q : Pattern) (selected : d58860 q = 0) : d59305 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58860, d59305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58860, d59305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58861 q = 0) : d59306 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58861, d59306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro265 q selected
    | true =>
      simp only [d58861, d59306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro287 q selected
  have h7 (q : Pattern) (selected : d58862 q = 0) : d59307 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58862, d59307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58862, d59307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d58863 q = 0) : d59308 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58863, d59308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58863, d59308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58864 q = 0) : d59309 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58864, d59309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58864, d59309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58866 q = 0) : d59311 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58866, d59311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58866, d59311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro290 q selected
  have h11 (q : Pattern) (selected : d58867 q = 0) : d59312 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58867, d59312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58867, d59312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d58868 q = 0) : d59313 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58868, d59313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58868, d59313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d58869 q = 0) : d59314 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58869, d59314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58869, d59314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro292 q selected
  have h14 (q : Pattern) (selected : d58870 q = 0) : d59315 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58870, d59315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d58870, d59315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d58871 q = 0) : d59316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58871, d59316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
    | true =>
      simp only [d58871, d59316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro295 q selected
  have h16 (q : Pattern) (selected : d58872 q = 0) : d59317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58872, d59317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d58872, d59317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d58873 q = 0) : d59318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58873, d59318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d58873, d59318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d58874 q = 0) : d59319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58874, d59319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d58874, d59319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d58875 q = 0) : d59320 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58875, d59320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58875, d59320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro1805 (p : Pattern) (selected : d58881 p = 0) : d59326 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58871 q = 0) : d59316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58871, d59316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro268 q selected
    | true =>
      simp only [d58871, d59316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro295 q selected
  have h2 (q : Pattern) (selected : d58872 q = 0) : d59317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58872, d59317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58872, d59317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58879 q = 0) : d59324 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58879, d59324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58879, d59324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58880 q = 0) : d59325 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58880, d59325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58880, d59325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58881 q = 0) : d59326 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58881, d59326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58881, d59326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1806 (p : Pattern) (selected : d58890 p = 0) : d59335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58886 q = 0) : d59331 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58886, d59331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro306 q selected
    | true =>
      simp only [d58886, d59331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro311 q selected
  have h2 (q : Pattern) (selected : d58887 q = 0) : d59332 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58887, d59332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58887, d59332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58888 q = 0) : d59333 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58888, d59333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58888, d59333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58889 q = 0) : d59334 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58889, d59334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58889, d59334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58890 q = 0) : d59335 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58890, d59335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58890, d59335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1807 (p : Pattern) (selected : d58895 p = 0) : d59340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58848 q = 0) : d59293 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58848, d59293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58848, d59293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1801 q selected
  have h2 (q : Pattern) (selected : d58854 q = 0) : d59299 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58854, d59299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1801 q selected
    | true =>
      simp only [d58854, d59299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1802 q selected
  have h3 (q : Pattern) (selected : d58855 q = 0) : d59300 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58855, d59300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58855, d59300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58876 q = 0) : d59321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58876, d59321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1803 q selected
    | true =>
      simp only [d58876, d59321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1804 q selected
  have h5 (q : Pattern) (selected : d58877 q = 0) : d59322 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58877, d59322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58877, d59322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58878 q = 0) : d59323 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58878, d59323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58878, d59323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58882 q = 0) : d59327 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58882, d59327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58882, d59327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1805 q selected
  have h8 (q : Pattern) (selected : d58883 q = 0) : d59328 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58883, d59328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d58883, d59328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d58884 q = 0) : d59329 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58884, d59329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58884, d59329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d58885 q = 0) : d59330 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58885, d59330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58885, d59330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d58891 q = 0) : d59336 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58891, d59336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58891, d59336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1806 q selected
  have h12 (q : Pattern) (selected : d58892 q = 0) : d59337 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58892, d59337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58892, d59337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d58893 q = 0) : d59338 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58893, d59338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d58893, d59338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d58894 q = 0) : d59339 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58894, d59339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d58894, d59339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d58895 q = 0) : d59340 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58895, d59340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58895, d59340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1808 (p : Pattern) (selected : d58901 p = 0) : d59346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58896 q = 0) : d59341 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58896, d59341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58896, d59341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1807 q selected
  have h2 (q : Pattern) (selected : d58897 q = 0) : d59342 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58897, d59342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58897, d59342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58898 q = 0) : d59343 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58898, d59343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58898, d59343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58899 q = 0) : d59344 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58899, d59344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58899, d59344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58900 q = 0) : d59345 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58900, d59345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58900, d59345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58901 q = 0) : d59346 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58901, d59346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58901, d59346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1809 (p : Pattern) (selected : d58907 p = 0) : d59352 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58903 q = 0) : d59348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58903, d59348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58903, d59348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d58904 q = 0) : d59349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58904, d59349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58904, d59349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58905 q = 0) : d59350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58905, d59350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58905, d59350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58906 q = 0) : d59351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58906, d59351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58906, d59351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58907 q = 0) : d59352 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58907, d59352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58907, d59352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1810 (p : Pattern) (selected : d58913 p = 0) : d59358 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58903 q = 0) : d59348 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58903, d59348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58903, d59348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro324 q selected
  have h2 (q : Pattern) (selected : d58904 q = 0) : d59349 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58904, d59349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58904, d59349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58905 q = 0) : d59350 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58905, d59350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58905, d59350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58906 q = 0) : d59351 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58906, d59351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58906, d59351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58909 q = 0) : d59354 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58909, d59354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58909, d59354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro327 q selected
  have h6 (q : Pattern) (selected : d58910 q = 0) : d59355 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58910, d59355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58910, d59355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58911 q = 0) : d59356 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58911, d59356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58911, d59356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58912 q = 0) : d59357 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58912, d59357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58912, d59357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58913 q = 0) : d59358 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58913, d59358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58913, d59358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1811 (p : Pattern) (selected : d58925 p = 0) : d59370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58916 q = 0) : d59361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58916, d59361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58916, d59361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d58917 q = 0) : d59362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58917, d59362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58917, d59362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58918 q = 0) : d59363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58918, d59363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58918, d59363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58919 q = 0) : d59364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58919, d59364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58919, d59364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro332 q selected
  have h5 (q : Pattern) (selected : d58920 q = 0) : d59365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58920, d59365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58920, d59365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58921 q = 0) : d59366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58921, d59366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d58921, d59366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h7 (q : Pattern) (selected : d58922 q = 0) : d59367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58922, d59367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58922, d59367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d58923 q = 0) : d59368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58923, d59368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58923, d59368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58924 q = 0) : d59369 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58924, d59369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58924, d59369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58925 q = 0) : d59370 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58925, d59370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58925, d59370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro1812 (p : Pattern) (selected : d58935 p = 0) : d59380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58916 q = 0) : d59361 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58916, d59361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58916, d59361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro330 q selected
  have h2 (q : Pattern) (selected : d58917 q = 0) : d59362 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58917, d59362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58917, d59362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58918 q = 0) : d59363 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58918, d59363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58918, d59363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58919 q = 0) : d59364 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58919, d59364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58919, d59364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro332 q selected
  have h5 (q : Pattern) (selected : d58920 q = 0) : d59365 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58920, d59365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58920, d59365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58921 q = 0) : d59366 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58921, d59366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro323 q selected
    | true =>
      simp only [d58921, d59366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro349 q selected
  have h7 (q : Pattern) (selected : d58922 q = 0) : d59367 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58922, d59367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58922, d59367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d58923 q = 0) : d59368 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58923, d59368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58923, d59368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58924 q = 0) : d59369 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58924, d59369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58924, d59369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58926 q = 0) : d59371 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58926, d59371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58926, d59371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro352 q selected
  have h11 (q : Pattern) (selected : d58927 q = 0) : d59372 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58927, d59372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58927, d59372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d58928 q = 0) : d59373 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58928, d59373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58928, d59373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d58929 q = 0) : d59374 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58929, d59374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58929, d59374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro354 q selected
  have h14 (q : Pattern) (selected : d58930 q = 0) : d59375 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58930, d59375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d58930, d59375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d58931 q = 0) : d59376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58931, d59376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
    | true =>
      simp only [d58931, d59376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro357 q selected
  have h16 (q : Pattern) (selected : d58932 q = 0) : d59377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58932, d59377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d58932, d59377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d58933 q = 0) : d59378 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58933, d59378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d58933, d59378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d58934 q = 0) : d59379 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58934, d59379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d58934, d59379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d58935 q = 0) : d59380 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58935, d59380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58935, d59380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro1813 (p : Pattern) (selected : d58941 p = 0) : d59386 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58931 q = 0) : d59376 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58931, d59376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro326 q selected
    | true =>
      simp only [d58931, d59376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro357 q selected
  have h2 (q : Pattern) (selected : d58932 q = 0) : d59377 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58932, d59377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58932, d59377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58939 q = 0) : d59384 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58939, d59384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58939, d59384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58940 q = 0) : d59385 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58940, d59385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58940, d59385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58941 q = 0) : d59386 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58941, d59386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58941, d59386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1814 (p : Pattern) (selected : d58950 p = 0) : d59395 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58946 q = 0) : d59391 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58946, d59391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro371 q selected
    | true =>
      simp only [d58946, d59391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro378 q selected
  have h2 (q : Pattern) (selected : d58947 q = 0) : d59392 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58947, d59392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58947, d59392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58948 q = 0) : d59393 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58948, d59393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58948, d59393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58949 q = 0) : d59394 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58949, d59394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58949, d59394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58950 q = 0) : d59395 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58950, d59395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58950, d59395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1815 (p : Pattern) (selected : d58955 p = 0) : d59400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58908 q = 0) : d59353 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58908, d59353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58908, d59353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1809 q selected
  have h2 (q : Pattern) (selected : d58914 q = 0) : d59359 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58914, d59359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1809 q selected
    | true =>
      simp only [d58914, d59359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1810 q selected
  have h3 (q : Pattern) (selected : d58915 q = 0) : d59360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58915, d59360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58915, d59360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58936 q = 0) : d59381 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58936, d59381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1811 q selected
    | true =>
      simp only [d58936, d59381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1812 q selected
  have h5 (q : Pattern) (selected : d58937 q = 0) : d59382 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58937, d59382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58937, d59382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58938 q = 0) : d59383 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58938, d59383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58938, d59383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58942 q = 0) : d59387 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58942, d59387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58942, d59387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1813 q selected
  have h8 (q : Pattern) (selected : d58943 q = 0) : d59388 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58943, d59388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d58943, d59388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d58944 q = 0) : d59389 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58944, d59389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58944, d59389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d58945 q = 0) : d59390 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58945, d59390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58945, d59390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d58951 q = 0) : d59396 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58951, d59396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58951, d59396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1814 q selected
  have h12 (q : Pattern) (selected : d58952 q = 0) : d59397 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58952, d59397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58952, d59397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d58953 q = 0) : d59398 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58953, d59398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d58953, d59398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d58954 q = 0) : d59399 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58954, d59399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d58954, d59399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d58955 q = 0) : d59400 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58955, d59400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58955, d59400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1816 (p : Pattern) (selected : d58961 p = 0) : d59406 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58956 q = 0) : d59401 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58956, d59401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58956, d59401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1815 q selected
  have h2 (q : Pattern) (selected : d58957 q = 0) : d59402 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58957, d59402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58957, d59402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58958 q = 0) : d59403 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58958, d59403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58958, d59403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58959 q = 0) : d59404 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58959, d59404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58959, d59404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58960 q = 0) : d59405 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58960, d59405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58960, d59405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58961 q = 0) : d59406 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58961, d59406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58961, d59406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1817 (p : Pattern) (selected : d58968 p = 0) : d59413 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58964 q = 0) : d59409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58964, d59409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58964, d59409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d58965 q = 0) : d59410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58965, d59410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58965, d59410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58966 q = 0) : d59411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58966, d59411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58966, d59411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58967 q = 0) : d59412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58967, d59412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58967, d59412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58968 q = 0) : d59413 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58968, d59413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58968, d59413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1818 (p : Pattern) (selected : d58974 p = 0) : d59419 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58964 q = 0) : d59409 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58964, d59409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58964, d59409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro396 q selected
  have h2 (q : Pattern) (selected : d58965 q = 0) : d59410 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58965, d59410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58965, d59410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58966 q = 0) : d59411 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58966, d59411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58966, d59411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58967 q = 0) : d59412 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58967, d59412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58967, d59412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58970 q = 0) : d59415 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58970, d59415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58970, d59415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro399 q selected
  have h6 (q : Pattern) (selected : d58971 q = 0) : d59416 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58971, d59416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58971, d59416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d58972 q = 0) : d59417 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58972, d59417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58972, d59417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58973 q = 0) : d59418 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58973, d59418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58973, d59418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58974 q = 0) : d59419 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58974, d59419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58974, d59419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1819 (p : Pattern) (selected : d58986 p = 0) : d59431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58977 q = 0) : d59422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58977, d59422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58977, d59422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d58978 q = 0) : d59423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58978, d59423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58978, d59423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58979 q = 0) : d59424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58979, d59424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58979, d59424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58980 q = 0) : d59425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58980, d59425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58980, d59425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro404 q selected
  have h5 (q : Pattern) (selected : d58981 q = 0) : d59426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58981, d59426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58981, d59426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58982 q = 0) : d59427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58982, d59427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d58982, d59427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h7 (q : Pattern) (selected : d58983 q = 0) : d59428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58983, d59428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58983, d59428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d58984 q = 0) : d59429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58984, d59429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58984, d59429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58985 q = 0) : d59430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58985, d59430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58985, d59430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58986 q = 0) : d59431 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58986, d59431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58986, d59431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro1820 (p : Pattern) (selected : d58996 p = 0) : d59441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58977 q = 0) : d59422 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58977, d59422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58977, d59422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro402 q selected
  have h2 (q : Pattern) (selected : d58978 q = 0) : d59423 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58978, d59423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58978, d59423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58979 q = 0) : d59424 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58979, d59424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58979, d59424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58980 q = 0) : d59425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58980, d59425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58980, d59425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro404 q selected
  have h5 (q : Pattern) (selected : d58981 q = 0) : d59426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58981, d59426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58981, d59426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58982 q = 0) : d59427 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58982, d59427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro395 q selected
    | true =>
      simp only [d58982, d59427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro425 q selected
  have h7 (q : Pattern) (selected : d58983 q = 0) : d59428 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58983, d59428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58983, d59428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d58984 q = 0) : d59429 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58984, d59429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58984, d59429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58985 q = 0) : d59430 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58985, d59430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58985, d59430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d58987 q = 0) : d59432 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58987, d59432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58987, d59432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro428 q selected
  have h11 (q : Pattern) (selected : d58988 q = 0) : d59433 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58988, d59433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58988, d59433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d58989 q = 0) : d59434 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58989, d59434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58989, d59434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d58990 q = 0) : d59435 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58990, d59435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58990, d59435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro430 q selected
  have h14 (q : Pattern) (selected : d58991 q = 0) : d59436 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58991, d59436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d58991, d59436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d58992 q = 0) : d59437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58992, d59437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
    | true =>
      simp only [d58992, d59437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro433 q selected
  have h16 (q : Pattern) (selected : d58993 q = 0) : d59438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58993, d59438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d58993, d59438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d58994 q = 0) : d59439 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58994, d59439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d58994, d59439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d58995 q = 0) : d59440 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58995, d59440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d58995, d59440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d58996 q = 0) : d59441 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58996, d59441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58996, d59441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro1821 (p : Pattern) (selected : d59002 p = 0) : d59447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58992 q = 0) : d59437 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58992, d59437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro398 q selected
    | true =>
      simp only [d58992, d59437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro433 q selected
  have h2 (q : Pattern) (selected : d58993 q = 0) : d59438 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58993, d59438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58993, d59438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59000 q = 0) : d59445 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59000, d59445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59000, d59445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59001 q = 0) : d59446 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59001, d59446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59001, d59446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59002 q = 0) : d59447 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59002, d59447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59002, d59447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1822 (p : Pattern) (selected : d59011 p = 0) : d59456 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59007 q = 0) : d59452 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59007, d59452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro447 q selected
    | true =>
      simp only [d59007, d59452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro454 q selected
  have h2 (q : Pattern) (selected : d59008 q = 0) : d59453 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59008, d59453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59008, d59453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59009 q = 0) : d59454 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59009, d59454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59009, d59454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59010 q = 0) : d59455 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59010, d59455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59010, d59455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59011 q = 0) : d59456 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59011, d59456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59011, d59456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1823 (p : Pattern) (selected : d59016 p = 0) : d59461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d58969 q = 0) : d59414 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58969, d59414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58969, d59414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1817 q selected
  have h2 (q : Pattern) (selected : d58975 q = 0) : d59420 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58975, d59420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1817 q selected
    | true =>
      simp only [d58975, d59420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1818 q selected
  have h3 (q : Pattern) (selected : d58976 q = 0) : d59421 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58976, d59421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58976, d59421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58997 q = 0) : d59442 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58997, d59442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1819 q selected
    | true =>
      simp only [d58997, d59442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1820 q selected
  have h5 (q : Pattern) (selected : d58998 q = 0) : d59443 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58998, d59443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58998, d59443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58999 q = 0) : d59444 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58999, d59444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58999, d59444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59003 q = 0) : d59448 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59003, d59448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59003, d59448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1821 q selected
  have h8 (q : Pattern) (selected : d59004 q = 0) : d59449 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59004, d59449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d59004, d59449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d59005 q = 0) : d59450 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59005, d59450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d59005, d59450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d59006 q = 0) : d59451 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59006, d59451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59006, d59451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d59012 q = 0) : d59457 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59012, d59457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59012, d59457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1822 q selected
  have h12 (q : Pattern) (selected : d59013 q = 0) : d59458 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59013, d59458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d59013, d59458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d59014 q = 0) : d59459 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59014, d59459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d59014, d59459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d59015 q = 0) : d59460 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59015, d59460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d59015, d59460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d59016 q = 0) : d59461 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59016, d59461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59016, d59461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1824 (p : Pattern) (selected : d59022 p = 0) : d59467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59017 q = 0) : d59462 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59017, d59462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59017, d59462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1823 q selected
  have h2 (q : Pattern) (selected : d59018 q = 0) : d59463 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59018, d59463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59018, d59463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d59019 q = 0) : d59464 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59019, d59464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59019, d59464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59020 q = 0) : d59465 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59020, d59465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59020, d59465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59021 q = 0) : d59466 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59021, d59466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59021, d59466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59022 q = 0) : d59467 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59022, d59467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59022, d59467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1825 (p : Pattern) (selected : d59030 p = 0) : d59475 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59026 q = 0) : d59471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59026, d59471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59026, d59471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d59027 q = 0) : d59472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59027, d59472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59027, d59472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59028 q = 0) : d59473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59028, d59473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59028, d59473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59029 q = 0) : d59474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59029, d59474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59029, d59474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59030 q = 0) : d59475 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59030, d59475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59030, d59475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1826 (p : Pattern) (selected : d59036 p = 0) : d59481 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59026 q = 0) : d59471 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59026, d59471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59026, d59471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro478 q selected
  have h2 (q : Pattern) (selected : d59027 q = 0) : d59472 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59027, d59472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59027, d59472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59028 q = 0) : d59473 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59028, d59473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59028, d59473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59029 q = 0) : d59474 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59029, d59474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59029, d59474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59032 q = 0) : d59477 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59032, d59477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59032, d59477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro481 q selected
  have h6 (q : Pattern) (selected : d59033 q = 0) : d59478 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59033, d59478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59033, d59478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d59034 q = 0) : d59479 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59034, d59479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59034, d59479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d59035 q = 0) : d59480 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59035, d59480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59035, d59480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59036 q = 0) : d59481 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59036, d59481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59036, d59481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1827 (p : Pattern) (selected : d59048 p = 0) : d59493 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59039 q = 0) : d59484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59039, d59484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59039, d59484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d59040 q = 0) : d59485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59040, d59485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59040, d59485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59041 q = 0) : d59486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59041, d59486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59041, d59486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59042 q = 0) : d59487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59042, d59487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59042, d59487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro486 q selected
  have h5 (q : Pattern) (selected : d59043 q = 0) : d59488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59043, d59488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59043, d59488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59044 q = 0) : d59489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59044, d59489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d59044, d59489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h7 (q : Pattern) (selected : d59045 q = 0) : d59490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59045, d59490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59045, d59490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d59046 q = 0) : d59491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59046, d59491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59046, d59491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59047 q = 0) : d59492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59047, d59492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59047, d59492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d59048 q = 0) : d59493 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59048, d59493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59048, d59493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro1828 (p : Pattern) (selected : d59058 p = 0) : d59503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59039 q = 0) : d59484 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59039, d59484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59039, d59484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro484 q selected
  have h2 (q : Pattern) (selected : d59040 q = 0) : d59485 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59040, d59485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59040, d59485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59041 q = 0) : d59486 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59041, d59486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59041, d59486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59042 q = 0) : d59487 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59042, d59487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59042, d59487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro486 q selected
  have h5 (q : Pattern) (selected : d59043 q = 0) : d59488 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59043, d59488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59043, d59488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59044 q = 0) : d59489 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59044, d59489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro477 q selected
    | true =>
      simp only [d59044, d59489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro511 q selected
  have h7 (q : Pattern) (selected : d59045 q = 0) : d59490 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59045, d59490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59045, d59490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d59046 q = 0) : d59491 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59046, d59491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59046, d59491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59047 q = 0) : d59492 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59047, d59492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59047, d59492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d59049 q = 0) : d59494 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59049, d59494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59049, d59494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro514 q selected
  have h11 (q : Pattern) (selected : d59050 q = 0) : d59495 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59050, d59495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59050, d59495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d59051 q = 0) : d59496 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59051, d59496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59051, d59496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d59052 q = 0) : d59497 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59052, d59497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59052, d59497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro516 q selected
  have h14 (q : Pattern) (selected : d59053 q = 0) : d59498 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59053, d59498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d59053, d59498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d59054 q = 0) : d59499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59054, d59499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
    | true =>
      simp only [d59054, d59499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro519 q selected
  have h16 (q : Pattern) (selected : d59055 q = 0) : d59500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59055, d59500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d59055, d59500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d59056 q = 0) : d59501 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59056, d59501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d59056, d59501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d59057 q = 0) : d59502 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59057, d59502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d59057, d59502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d59058 q = 0) : d59503 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59058, d59503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d59058, d59503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro1829 (p : Pattern) (selected : d59064 p = 0) : d59509 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59054 q = 0) : d59499 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59054, d59499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro480 q selected
    | true =>
      simp only [d59054, d59499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro519 q selected
  have h2 (q : Pattern) (selected : d59055 q = 0) : d59500 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59055, d59500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59055, d59500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59062 q = 0) : d59507 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59062, d59507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59062, d59507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59063 q = 0) : d59508 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59063, d59508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59063, d59508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59064 q = 0) : d59509 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59064, d59509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59064, d59509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1830 (p : Pattern) (selected : d59073 p = 0) : d59518 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59069 q = 0) : d59514 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59069, d59514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro533 q selected
    | true =>
      simp only [d59069, d59514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro540 q selected
  have h2 (q : Pattern) (selected : d59070 q = 0) : d59515 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59070, d59515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59070, d59515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59071 q = 0) : d59516 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59071, d59516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59071, d59516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59072 q = 0) : d59517 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59072, d59517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59072, d59517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59073 q = 0) : d59518 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59073, d59518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59073, d59518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1831 (p : Pattern) (selected : d59078 p = 0) : d59523 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59031 q = 0) : d59476 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59031, d59476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59031, d59476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1825 q selected
  have h2 (q : Pattern) (selected : d59037 q = 0) : d59482 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59037, d59482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1825 q selected
    | true =>
      simp only [d59037, d59482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1826 q selected
  have h3 (q : Pattern) (selected : d59038 q = 0) : d59483 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59038, d59483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59038, d59483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59059 q = 0) : d59504 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59059, d59504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1827 q selected
    | true =>
      simp only [d59059, d59504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1828 q selected
  have h5 (q : Pattern) (selected : d59060 q = 0) : d59505 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59060, d59505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59060, d59505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59061 q = 0) : d59506 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59061, d59506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59061, d59506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59065 q = 0) : d59510 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59065, d59510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59065, d59510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1829 q selected
  have h8 (q : Pattern) (selected : d59066 q = 0) : d59511 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59066, d59511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d59066, d59511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d59067 q = 0) : d59512 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59067, d59512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d59067, d59512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d59068 q = 0) : d59513 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59068, d59513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59068, d59513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d59074 q = 0) : d59519 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59074, d59519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59074, d59519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1830 q selected
  have h12 (q : Pattern) (selected : d59075 q = 0) : d59520 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59075, d59520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d59075, d59520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d59076 q = 0) : d59521 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59076, d59521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d59076, d59521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d59077 q = 0) : d59522 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59077, d59522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d59077, d59522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d59078 q = 0) : d59523 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59078, d59523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59078, d59523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1832 (p : Pattern) (selected : d59084 p = 0) : d59529 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59079 q = 0) : d59524 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59079, d59524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59079, d59524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1831 q selected
  have h2 (q : Pattern) (selected : d59080 q = 0) : d59525 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59080, d59525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59080, d59525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d59081 q = 0) : d59526 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59081, d59526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59081, d59526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59082 q = 0) : d59527 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59082, d59527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59082, d59527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59083 q = 0) : d59528 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59083, d59528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59083, d59528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59084 q = 0) : d59529 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59084, d59529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59084, d59529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1833 (p : Pattern) (selected : d59093 p = 0) : d59538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59089 q = 0) : d59534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59089, d59534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59089, d59534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d59090 q = 0) : d59535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59090, d59535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59090, d59535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59091 q = 0) : d59536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59091, d59536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59091, d59536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59092 q = 0) : d59537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59092, d59537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59092, d59537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59093 q = 0) : d59538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59093, d59538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59093, d59538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1834 (p : Pattern) (selected : d59099 p = 0) : d59544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59089 q = 0) : d59534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59089, d59534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59089, d59534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro567 q selected
  have h2 (q : Pattern) (selected : d59090 q = 0) : d59535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59090, d59535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59090, d59535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59091 q = 0) : d59536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59091, d59536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59091, d59536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59092 q = 0) : d59537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59092, d59537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59092, d59537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59095 q = 0) : d59540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59095, d59540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59095, d59540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro570 q selected
  have h6 (q : Pattern) (selected : d59096 q = 0) : d59541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59096, d59541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59096, d59541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d59097 q = 0) : d59542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59097, d59542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59097, d59542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d59098 q = 0) : d59543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59098, d59543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59098, d59543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59099 q = 0) : d59544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59099, d59544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59099, d59544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro1835 (p : Pattern) (selected : d59111 p = 0) : d59556 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59102 q = 0) : d59547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59102, d59547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59102, d59547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d59103 q = 0) : d59548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59103, d59548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59103, d59548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59104 q = 0) : d59549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59104, d59549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59104, d59549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59105 q = 0) : d59550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59105, d59550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59105, d59550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro575 q selected
  have h5 (q : Pattern) (selected : d59106 q = 0) : d59551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59106, d59551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59106, d59551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59107 q = 0) : d59552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59107, d59552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d59107, d59552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h7 (q : Pattern) (selected : d59108 q = 0) : d59553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59108, d59553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59108, d59553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d59109 q = 0) : d59554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59109, d59554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59109, d59554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59110 q = 0) : d59555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59110, d59555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59110, d59555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d59111 q = 0) : d59556 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59111, d59556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59111, d59556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro1836 (p : Pattern) (selected : d59121 p = 0) : d59566 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59102 q = 0) : d59547 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59102, d59547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59102, d59547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro573 q selected
  have h2 (q : Pattern) (selected : d59103 q = 0) : d59548 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59103, d59548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59103, d59548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59104 q = 0) : d59549 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59104, d59549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59104, d59549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59105 q = 0) : d59550 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59105, d59550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59105, d59550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro575 q selected
  have h5 (q : Pattern) (selected : d59106 q = 0) : d59551 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59106, d59551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59106, d59551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59107 q = 0) : d59552 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59107, d59552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro566 q selected
    | true =>
      simp only [d59107, d59552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro601 q selected
  have h7 (q : Pattern) (selected : d59108 q = 0) : d59553 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59108, d59553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59108, d59553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d59109 q = 0) : d59554 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59109, d59554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59109, d59554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59110 q = 0) : d59555 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59110, d59555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59110, d59555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d59112 q = 0) : d59557 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59112, d59557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59112, d59557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro604 q selected
  have h11 (q : Pattern) (selected : d59113 q = 0) : d59558 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59113, d59558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59113, d59558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d59114 q = 0) : d59559 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59114, d59559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59114, d59559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d59115 q = 0) : d59560 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59115, d59560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59115, d59560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro606 q selected
  have h14 (q : Pattern) (selected : d59116 q = 0) : d59561 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59116, d59561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d59116, d59561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d59117 q = 0) : d59562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59117, d59562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
    | true =>
      simp only [d59117, d59562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro609 q selected
  have h16 (q : Pattern) (selected : d59118 q = 0) : d59563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59118, d59563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d59118, d59563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d59119 q = 0) : d59564 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59119, d59564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d59119, d59564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d59120 q = 0) : d59565 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59120, d59565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d59120, d59565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d59121 q = 0) : d59566 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59121, d59566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d59121, d59566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro1837 (p : Pattern) (selected : d59127 p = 0) : d59572 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59117 q = 0) : d59562 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59117, d59562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro569 q selected
    | true =>
      simp only [d59117, d59562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro609 q selected
  have h2 (q : Pattern) (selected : d59118 q = 0) : d59563 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59118, d59563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59118, d59563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59125 q = 0) : d59570 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59125, d59570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59125, d59570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59126 q = 0) : d59571 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59126, d59571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59126, d59571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59127 q = 0) : d59572 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59127, d59572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59127, d59572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1838 (p : Pattern) (selected : d59136 p = 0) : d59581 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59132 q = 0) : d59577 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59132, d59577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro623 q selected
    | true =>
      simp only [d59132, d59577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro630 q selected
  have h2 (q : Pattern) (selected : d59133 q = 0) : d59578 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59133, d59578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59133, d59578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59134 q = 0) : d59579 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59134, d59579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59134, d59579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59135 q = 0) : d59580 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59135, d59580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59135, d59580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59136 q = 0) : d59581 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59136, d59581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59136, d59581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  exact h5 p selected
theorem eqIntro1839 (p : Pattern) (selected : d59141 p = 0) : d59586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59094 q = 0) : d59539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59094, d59539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59094, d59539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1833 q selected
  have h2 (q : Pattern) (selected : d59100 q = 0) : d59545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59100, d59545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1833 q selected
    | true =>
      simp only [d59100, d59545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1834 q selected
  have h3 (q : Pattern) (selected : d59101 q = 0) : d59546 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59101, d59546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59101, d59546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59122 q = 0) : d59567 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59122, d59567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1835 q selected
    | true =>
      simp only [d59122, d59567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1836 q selected
  have h5 (q : Pattern) (selected : d59123 q = 0) : d59568 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59123, d59568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59123, d59568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59124 q = 0) : d59569 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59124, d59569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59124, d59569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59128 q = 0) : d59573 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59128, d59573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59128, d59573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1837 q selected
  have h8 (q : Pattern) (selected : d59129 q = 0) : d59574 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59129, d59574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d59129, d59574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d59130 q = 0) : d59575 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59130, d59575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d59130, d59575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d59131 q = 0) : d59576 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59131, d59576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59131, d59576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d59137 q = 0) : d59582 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59137, d59582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59137, d59582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1838 q selected
  have h12 (q : Pattern) (selected : d59138 q = 0) : d59583 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59138, d59583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d59138, d59583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d59139 q = 0) : d59584 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59139, d59584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d59139, d59584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d59140 q = 0) : d59585 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59140, d59585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d59140, d59585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d59141 q = 0) : d59586 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59141, d59586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59141, d59586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1840 (p : Pattern) (selected : d59147 p = 0) : d59592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59142 q = 0) : d59587 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59142, d59587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59142, d59587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1839 q selected
  have h2 (q : Pattern) (selected : d59143 q = 0) : d59588 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59143, d59588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59143, d59588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d59144 q = 0) : d59589 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59144, d59589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59144, d59589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59145 q = 0) : d59590 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59145, d59590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59145, d59590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59146 q = 0) : d59591 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59146, d59591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59146, d59591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59147 q = 0) : d59592 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59147, d59592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59147, d59592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1841 (p : Pattern) (selected : d59153 p = 0) : d59598 p = 1 := by
  have h0 (q : Pattern) (selected : d58902 q = 0) : d59347 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58902, d59347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1800 q selected
    | true =>
      simp only [d58902, d59347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1808 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d58962 q = 0) : d59407 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58962, d59407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58962, d59407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1816 q selected
  have h3 (q : Pattern) (selected : d58963 q = 0) : d59408 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58963, d59408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58963, d59408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59023 q = 0) : d59468 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59023, d59468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59023, d59468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1824 q selected
  have h5 (q : Pattern) (selected : d59024 q = 0) : d59469 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59024, d59469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59024, d59469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59025 q = 0) : d59470 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59025, d59470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59025, d59470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59085 q = 0) : d59530 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59085, d59530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59085, d59530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1832 q selected
  have h8 (q : Pattern) (selected : d59086 q = 0) : d59531 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59086, d59531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59086, d59531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59087 q = 0) : d59532 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59087, d59532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59087, d59532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d59088 q = 0) : d59533 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d59088, d59533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59088, d59533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d59148 q = 0) : d59593 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59148, d59593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59148, d59593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1840 q selected
  have h12 (q : Pattern) (selected : d59149 q = 0) : d59594 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59149, d59594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59149, d59594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d59150 q = 0) : d59595 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59150, d59595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59150, d59595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d59151 q = 0) : d59596 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d59151, d59596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59151, d59596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d59152 q = 0) : d59597 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d59152, d59597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59152, d59597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d59153 q = 0) : d59598 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d59153, d59598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d59153, d59598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1842 (p : Pattern) (selected : d59159 p = 0) : d59604 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59154 q = 0) : d59599 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d59154, d59599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1841 q selected
    | true =>
      simp only [d59154, d59599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59155 q = 0) : d59600 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d59155, d59600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59155, d59600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59156 q = 0) : d59601 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d59156, d59601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59156, d59601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59157 q = 0) : d59602 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d59157, d59602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59157, d59602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59158 q = 0) : d59603 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d59158, d59603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59158, d59603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59159 q = 0) : d59604 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d59159, d59604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59159, d59604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1843 (p : Pattern) (selected : d59165 p = 0) : d59610 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59160 q = 0) : d59605 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d59160, d59605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1842 q selected
    | true =>
      simp only [d59160, d59605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59161 q = 0) : d59606 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d59161, d59606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59161, d59606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59162 q = 0) : d59607 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d59162, d59607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59162, d59607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59163 q = 0) : d59608 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d59163, d59608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59163, d59608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59164 q = 0) : d59609 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d59164, d59609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59164, d59609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59165 q = 0) : d59610 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d59165, d59610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59165, d59610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1844 (p : Pattern) (selected : d59171 p = 0) : d59616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59166 q = 0) : d59611 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d59166, d59611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1843 q selected
    | true =>
      simp only [d59166, d59611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59167 q = 0) : d59612 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d59167, d59612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59167, d59612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59168 q = 0) : d59613 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d59168, d59613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59168, d59613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59169 q = 0) : d59614 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d59169, d59614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59169, d59614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59170 q = 0) : d59615 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d59170, d59615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59170, d59615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59171 q = 0) : d59616 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d59171, d59616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59171, d59616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1845 (p : Pattern) (selected : d59177 p = 0) : d59622 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59172 q = 0) : d59617 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d59172, d59617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1844 q selected
    | true =>
      simp only [d59172, d59617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59173 q = 0) : d59618 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d59173, d59618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59173, d59618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59174 q = 0) : d59619 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d59174, d59619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59174, d59619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59175 q = 0) : d59620 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d59175, d59620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59175, d59620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59176 q = 0) : d59621 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d59176, d59621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59176, d59621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59177 q = 0) : d59622 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d59177, d59622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59177, d59622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1846 (p : Pattern) (selected : d59183 p = 0) : d59628 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59178 q = 0) : d59623 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d59178, d59623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1845 q selected
    | true =>
      simp only [d59178, d59623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59179 q = 0) : d59624 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d59179, d59624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59179, d59624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59180 q = 0) : d59625 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d59180, d59625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59180, d59625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59181 q = 0) : d59626 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d59181, d59626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59181, d59626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59182 q = 0) : d59627 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d59182, d59627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59182, d59627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59183 q = 0) : d59628 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d59183, d59628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59183, d59628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1847 (p : Pattern) (selected : d59189 p = 0) : d59634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59184 q = 0) : d59629 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d59184, d59629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1846 q selected
    | true =>
      simp only [d59184, d59629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59185 q = 0) : d59630 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d59185, d59630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59185, d59630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59186 q = 0) : d59631 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d59186, d59631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59186, d59631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59187 q = 0) : d59632 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d59187, d59632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59187, d59632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59188 q = 0) : d59633 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d59188, d59633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59188, d59633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59189 q = 0) : d59634 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d59189, d59634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59189, d59634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1848 (p : Pattern) (selected : d59195 p = 0) : d59640 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d59190 q = 0) : d59635 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d59190, d59635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1847 q selected
    | true =>
      simp only [d59190, d59635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59191 q = 0) : d59636 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d59191, d59636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59191, d59636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59192 q = 0) : d59637 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d59192, d59637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59192, d59637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59193 q = 0) : d59638 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d59193, d59638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59193, d59638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59194 q = 0) : d59639 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d59194, d59639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59194, d59639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59195 q = 0) : d59640 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d59195, d59640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59195, d59640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1849 (p : Pattern) (selected : d58806 p = 1) : d59969 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58799 q = 1) : d58799 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58801 q = 1) : d58801 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d156 q = 1) : d156 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d58802 q = 1) : d59965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58802, d59965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58802, d59965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h5 (q : Pattern) (selected : d58803 q = 1) : d59966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58803, d59966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58803, d59966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58804 q = 1) : d59967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58804, d59967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58804, d59967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58805 q = 1) : d59968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58805, d59968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58805, d59968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58806 q = 1) : d59969 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58806, d59969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58806, d59969, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1850 (p : Pattern) (selected : d58816 p = 1) : d59974 p = 1 := by
  have h0 (q : Pattern) (selected : d58799 q = 1) : d58799 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58801 q = 1) : d58801 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d156 q = 1) : d156 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d58802 q = 1) : d59965 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58802, d59965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58802, d59965, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro4 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d58803 q = 1) : d59966 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58803, d59966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58803, d59966, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58804 q = 1) : d59967 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58804, d59967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58804, d59967, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58805 q = 1) : d59968 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58805, d59968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58805, d59968, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58809 q = 1) : d58809 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d58811 q = 1) : d58811 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d203 q = 1) : d203 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d58812 q = 1) : d59970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58812, d59970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58812, d59970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h12 (q : Pattern) (selected : d58813 q = 1) : d59971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58813, d59971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58813, d59971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h13 (q : Pattern) (selected : d58814 q = 1) : d59972 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58814, d59972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58814, d59972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d58815 q = 1) : d59973 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58815, d59973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58815, d59973, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d58816 q = 1) : d59974 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58816, d59974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d58816, d59974, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1851 (p : Pattern) (selected : d58822 p = 1) : d59980 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d203 q = 1) : d203 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58812 q = 1) : d59970 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58812, d59970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58812, d59970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro6 q selected
  have h3 (q : Pattern) (selected : d58813 q = 1) : d59971 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58813, d59971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58813, d59971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58820 q = 1) : d59978 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58820, d59978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58820, d59978, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58821 q = 1) : d59979 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58821, d59979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58821, d59979, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58822 q = 1) : d59980 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58822, d59980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58822, d59980, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1852 (p : Pattern) (selected : d58831 p = 1) : d59989 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d243 q = 1) : d243 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58827 q = 1) : d59985 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58827, d59985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58827, d59985, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro11 q selected
  have h3 (q : Pattern) (selected : d58828 q = 1) : d59986 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58828, d59986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58828, d59986, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58829 q = 1) : d59987 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58829, d59987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58829, d59987, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58830 q = 1) : d59988 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58830, d59988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58830, d59988, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58831 q = 1) : d59989 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58831, d59989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58831, d59989, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1853 (p : Pattern) (selected : d58836 p = 1) : d59994 p = 1 := by
  have h0 (q : Pattern) (selected : d58796 q = 1) : d58796 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58817 q = 1) : d59975 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58817, d59975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1849 q selected
    | true =>
      simp only [d58817, d59975, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1850 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d58818 q = 1) : d59976 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58818, d59976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58818, d59976, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58819 q = 1) : d59977 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58819, d59977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58819, d59977, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58823 q = 1) : d59981 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58823, d59981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58823, d59981, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1851 q selected
  have h6 (q : Pattern) (selected : d58824 q = 1) : d59982 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58824, d59982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58824, d59982, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d58825 q = 1) : d59983 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58825, d59983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58825, d59983, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d58826 q = 1) : d59984 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58826, d59984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58826, d59984, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58832 q = 1) : d59990 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58832, d59990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58832, d59990, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1852 q selected
  have h10 (q : Pattern) (selected : d58833 q = 1) : d59991 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58833, d59991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58833, d59991, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h11 (q : Pattern) (selected : d58834 q = 1) : d59992 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58834, d59992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58834, d59992, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h12 (q : Pattern) (selected : d58835 q = 1) : d59993 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58835, d59993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58835, d59993, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d58836 q = 1) : d59994 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58836, d59994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58836, d59994, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro1854 (p : Pattern) (selected : d58842 p = 1) : d60000 p = 1 := by
  have h0 (q : Pattern) (selected : d58783 q = 1) : d58783 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58837 q = 1) : d59995 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58837, d59995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58837, d59995, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1853 q selected
  have h3 (q : Pattern) (selected : d58838 q = 1) : d59996 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58838, d59996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58838, d59996, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58839 q = 1) : d59997 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58839, d59997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58839, d59997, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58840 q = 1) : d59998 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58840, d59998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58840, d59998, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58841 q = 1) : d59999 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58841, d59999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58841, d59999, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58842 q = 1) : d60000 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58842, d60000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58842, d60000, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro1855 (p : Pattern) (selected : d58865 p = 1) : d60005 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58858 q = 1) : d58858 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58860 q = 1) : d58860 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d487 q = 1) : d487 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d58861 q = 1) : d60001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58861, d60001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58861, d60001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h5 (q : Pattern) (selected : d58862 q = 1) : d60002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58862, d60002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58862, d60002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58863 q = 1) : d60003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58863, d60003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58863, d60003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58864 q = 1) : d60004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58864, d60004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58864, d60004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58865 q = 1) : d60005 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58865, d60005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58865, d60005, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1856 (p : Pattern) (selected : d58875 p = 1) : d60010 p = 1 := by
  have h0 (q : Pattern) (selected : d58858 q = 1) : d58858 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58860 q = 1) : d58860 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d487 q = 1) : d487 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d58861 q = 1) : d60001 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58861, d60001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58861, d60001, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro35 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d58862 q = 1) : d60002 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58862, d60002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58862, d60002, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58863 q = 1) : d60003 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58863, d60003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58863, d60003, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58864 q = 1) : d60004 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58864, d60004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58864, d60004, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58868 q = 1) : d58868 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d58870 q = 1) : d58870 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d500 q = 1) : d500 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d58871 q = 1) : d60006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58871, d60006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58871, d60006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38 q selected
  have h12 (q : Pattern) (selected : d58872 q = 1) : d60007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58872, d60007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58872, d60007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h13 (q : Pattern) (selected : d58873 q = 1) : d60008 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58873, d60008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58873, d60008, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d58874 q = 1) : d60009 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58874, d60009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58874, d60009, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d58875 q = 1) : d60010 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58875, d60010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d58875, d60010, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1857 (p : Pattern) (selected : d58881 p = 1) : d60016 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d500 q = 1) : d500 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58871 q = 1) : d60006 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58871, d60006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58871, d60006, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro38 q selected
  have h3 (q : Pattern) (selected : d58872 q = 1) : d60007 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58872, d60007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58872, d60007, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58879 q = 1) : d60014 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58879, d60014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58879, d60014, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58880 q = 1) : d60015 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58880, d60015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58880, d60015, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58881 q = 1) : d60016 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58881, d60016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58881, d60016, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1858 (p : Pattern) (selected : d58890 p = 1) : d60025 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d689 q = 1) : d689 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58886 q = 1) : d60021 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58886, d60021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58886, d60021, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro45 q selected
  have h3 (q : Pattern) (selected : d58887 q = 1) : d60022 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58887, d60022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58887, d60022, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58888 q = 1) : d60023 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58888, d60023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58888, d60023, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58889 q = 1) : d60024 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58889, d60024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58889, d60024, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58890 q = 1) : d60025 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58890, d60025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58890, d60025, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1859 (p : Pattern) (selected : d58895 p = 1) : d60030 p = 1 := by
  have h0 (q : Pattern) (selected : d58855 q = 1) : d58855 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58876 q = 1) : d60011 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58876, d60011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1855 q selected
    | true =>
      simp only [d58876, d60011, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1856 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d58877 q = 1) : d60012 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58877, d60012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58877, d60012, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58878 q = 1) : d60013 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58878, d60013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58878, d60013, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58882 q = 1) : d60017 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58882, d60017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58882, d60017, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1857 q selected
  have h6 (q : Pattern) (selected : d58883 q = 1) : d60018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58883, d60018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58883, d60018, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d58884 q = 1) : d60019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58884, d60019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58884, d60019, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d58885 q = 1) : d60020 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58885, d60020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58885, d60020, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58891 q = 1) : d60026 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58891, d60026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58891, d60026, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1858 q selected
  have h10 (q : Pattern) (selected : d58892 q = 1) : d60027 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58892, d60027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58892, d60027, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h11 (q : Pattern) (selected : d58893 q = 1) : d60028 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58893, d60028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58893, d60028, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h12 (q : Pattern) (selected : d58894 q = 1) : d60029 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58894, d60029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58894, d60029, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d58895 q = 1) : d60030 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58895, d60030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58895, d60030, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro1860 (p : Pattern) (selected : d58901 p = 1) : d60036 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58896 q = 1) : d60031 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58896, d60031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58896, d60031, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1859 q selected
  have h2 (q : Pattern) (selected : d58897 q = 1) : d60032 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58897, d60032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58897, d60032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58898 q = 1) : d60033 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58898, d60033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58898, d60033, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58899 q = 1) : d60034 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58899, d60034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58899, d60034, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58900 q = 1) : d60035 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58900, d60035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58900, d60035, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58901 q = 1) : d60036 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58901, d60036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58901, d60036, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1861 (p : Pattern) (selected : d58925 p = 1) : d60042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58918 q = 1) : d58918 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58920 q = 1) : d58920 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d779 q = 1) : d779 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d58921 q = 1) : d60038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58921, d60038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58921, d60038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h5 (q : Pattern) (selected : d58922 q = 1) : d60039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58922, d60039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58922, d60039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58923 q = 1) : d60040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58923, d60040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58923, d60040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58924 q = 1) : d60041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58924, d60041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58924, d60041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58925 q = 1) : d60042 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58925, d60042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58925, d60042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1862 (p : Pattern) (selected : d58935 p = 1) : d60047 p = 1 := by
  have h0 (q : Pattern) (selected : d58918 q = 1) : d58918 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58920 q = 1) : d58920 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d779 q = 1) : d779 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d58921 q = 1) : d60038 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58921, d60038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58921, d60038, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro59 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d58922 q = 1) : d60039 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58922, d60039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58922, d60039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58923 q = 1) : d60040 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58923, d60040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58923, d60040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58924 q = 1) : d60041 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58924, d60041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58924, d60041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58928 q = 1) : d58928 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d58930 q = 1) : d58930 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d792 q = 1) : d792 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d58931 q = 1) : d60043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58931, d60043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58931, d60043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro62 q selected
  have h12 (q : Pattern) (selected : d58932 q = 1) : d60044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58932, d60044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58932, d60044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h13 (q : Pattern) (selected : d58933 q = 1) : d60045 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58933, d60045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58933, d60045, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d58934 q = 1) : d60046 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58934, d60046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58934, d60046, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d58935 q = 1) : d60047 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58935, d60047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d58935, d60047, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1863 (p : Pattern) (selected : d58941 p = 1) : d60053 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d792 q = 1) : d792 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58931 q = 1) : d60043 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58931, d60043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58931, d60043, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro62 q selected
  have h3 (q : Pattern) (selected : d58932 q = 1) : d60044 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58932, d60044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58932, d60044, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58939 q = 1) : d60051 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58939, d60051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58939, d60051, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58940 q = 1) : d60052 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58940, d60052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58940, d60052, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58941 q = 1) : d60053 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58941, d60053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58941, d60053, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1864 (p : Pattern) (selected : d58950 p = 1) : d60062 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1011 q = 1) : d1011 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58946 q = 1) : d60058 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58946, d60058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58946, d60058, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro71 q selected
  have h3 (q : Pattern) (selected : d58947 q = 1) : d60059 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58947, d60059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58947, d60059, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d58948 q = 1) : d60060 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58948, d60060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58948, d60060, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58949 q = 1) : d60061 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58949, d60061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58949, d60061, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58950 q = 1) : d60062 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58950, d60062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58950, d60062, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1865 (p : Pattern) (selected : d58955 p = 1) : d60067 p = 1 := by
  have h0 (q : Pattern) (selected : d58915 q = 1) : d58915 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58936 q = 1) : d60048 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58936, d60048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1861 q selected
    | true =>
      simp only [d58936, d60048, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1862 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d58937 q = 1) : d60049 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58937, d60049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58937, d60049, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58938 q = 1) : d60050 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58938, d60050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58938, d60050, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58942 q = 1) : d60054 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58942, d60054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58942, d60054, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1863 q selected
  have h6 (q : Pattern) (selected : d58943 q = 1) : d60055 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58943, d60055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d58943, d60055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d58944 q = 1) : d60056 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58944, d60056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d58944, d60056, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d58945 q = 1) : d60057 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58945, d60057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58945, d60057, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d58951 q = 1) : d60063 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58951, d60063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58951, d60063, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1864 q selected
  have h10 (q : Pattern) (selected : d58952 q = 1) : d60064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58952, d60064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58952, d60064, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h11 (q : Pattern) (selected : d58953 q = 1) : d60065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58953, d60065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58953, d60065, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h12 (q : Pattern) (selected : d58954 q = 1) : d60066 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d58954, d60066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58954, d60066, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d58955 q = 1) : d60067 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d58955, d60067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58955, d60067, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro1866 (p : Pattern) (selected : d58961 p = 1) : d60073 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58956 q = 1) : d60068 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d58956, d60068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58956, d60068, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1865 q selected
  have h2 (q : Pattern) (selected : d58957 q = 1) : d60069 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d58957, d60069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58957, d60069, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d58958 q = 1) : d60070 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d58958, d60070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58958, d60070, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58959 q = 1) : d60071 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d58959, d60071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58959, d60071, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d58960 q = 1) : d60072 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d58960, d60072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58960, d60072, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58961 q = 1) : d60073 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d58961, d60073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58961, d60073, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1867 (p : Pattern) (selected : d58986 p = 1) : d60080 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58979 q = 1) : d58979 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58981 q = 1) : d58981 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1158 q = 1) : d1158 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d58982 q = 1) : d60076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58982, d60076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58982, d60076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h5 (q : Pattern) (selected : d58983 q = 1) : d60077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58983, d60077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d58983, d60077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d58984 q = 1) : d60078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58984, d60078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58984, d60078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58985 q = 1) : d60079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58985, d60079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58985, d60079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58986 q = 1) : d60080 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58986, d60080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58986, d60080, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1868 (p : Pattern) (selected : d58996 p = 1) : d60085 p = 1 := by
  have h0 (q : Pattern) (selected : d58979 q = 1) : d58979 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58981 q = 1) : d58981 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1158 q = 1) : d1158 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d58982 q = 1) : d60076 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58982, d60076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58982, d60076, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro89 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d58983 q = 1) : d60077 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58983, d60077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d58983, d60077, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d58984 q = 1) : d60078 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58984, d60078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58984, d60078, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d58985 q = 1) : d60079 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58985, d60079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58985, d60079, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d58989 q = 1) : d58989 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d58991 q = 1) : d58991 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d1171 q = 1) : d1171 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d58992 q = 1) : d60081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58992, d60081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d58992, d60081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro92 q selected
  have h12 (q : Pattern) (selected : d58993 q = 1) : d60082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58993, d60082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d58993, d60082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h13 (q : Pattern) (selected : d58994 q = 1) : d60083 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d58994, d60083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d58994, d60083, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d58995 q = 1) : d60084 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d58995, d60084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d58995, d60084, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d58996 q = 1) : d60085 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d58996, d60085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d58996, d60085, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1869 (p : Pattern) (selected : d59002 p = 1) : d60091 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1171 q = 1) : d1171 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58992 q = 1) : d60081 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d58992, d60081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58992, d60081, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro92 q selected
  have h3 (q : Pattern) (selected : d58993 q = 1) : d60082 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d58993, d60082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58993, d60082, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59000 q = 1) : d60089 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59000, d60089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59000, d60089, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59001 q = 1) : d60090 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59001, d60090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59001, d60090, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59002 q = 1) : d60091 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59002, d60091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59002, d60091, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1870 (p : Pattern) (selected : d59011 p = 1) : d60100 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1436 q = 1) : d1436 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d59007 q = 1) : d60096 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59007, d60096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59007, d60096, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro101 q selected
  have h3 (q : Pattern) (selected : d59008 q = 1) : d60097 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59008, d60097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59008, d60097, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59009 q = 1) : d60098 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59009, d60098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59009, d60098, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59010 q = 1) : d60099 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59010, d60099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59010, d60099, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59011 q = 1) : d60100 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59011, d60100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59011, d60100, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1871 (p : Pattern) (selected : d59016 p = 1) : d60105 p = 1 := by
  have h0 (q : Pattern) (selected : d58976 q = 1) : d58976 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d58997 q = 1) : d60086 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d58997, d60086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1867 q selected
    | true =>
      simp only [d58997, d60086, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1868 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d58998 q = 1) : d60087 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58998, d60087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58998, d60087, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d58999 q = 1) : d60088 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d58999, d60088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58999, d60088, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59003 q = 1) : d60092 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59003, d60092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59003, d60092, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1869 q selected
  have h6 (q : Pattern) (selected : d59004 q = 1) : d60093 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59004, d60093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59004, d60093, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d59005 q = 1) : d60094 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59005, d60094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59005, d60094, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d59006 q = 1) : d60095 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59006, d60095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59006, d60095, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59012 q = 1) : d60101 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59012, d60101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59012, d60101, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1870 q selected
  have h10 (q : Pattern) (selected : d59013 q = 1) : d60102 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59013, d60102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d59013, d60102, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h11 (q : Pattern) (selected : d59014 q = 1) : d60103 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59014, d60103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59014, d60103, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h12 (q : Pattern) (selected : d59015 q = 1) : d60104 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59015, d60104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d59015, d60104, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d59016 q = 1) : d60105 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59016, d60105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d59016, d60105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro1872 (p : Pattern) (selected : d59022 p = 1) : d60111 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59017 q = 1) : d60106 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59017, d60106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59017, d60106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1871 q selected
  have h2 (q : Pattern) (selected : d59018 q = 1) : d60107 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59018, d60107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59018, d60107, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d59019 q = 1) : d60108 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59019, d60108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59019, d60108, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59020 q = 1) : d60109 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59020, d60109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59020, d60109, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59021 q = 1) : d60110 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59021, d60110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59021, d60110, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59022 q = 1) : d60111 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59022, d60111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59022, d60111, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1873 (p : Pattern) (selected : d59048 p = 1) : d60119 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59041 q = 1) : d59041 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d59043 q = 1) : d59043 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1619 q = 1) : d1619 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d59044 q = 1) : d60115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59044, d60115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59044, d60115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h5 (q : Pattern) (selected : d59045 q = 1) : d60116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59045, d60116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59045, d60116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59046 q = 1) : d60117 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59046, d60117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59046, d60117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59047 q = 1) : d60118 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59047, d60118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59047, d60118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d59048 q = 1) : d60119 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59048, d60119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59048, d60119, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1874 (p : Pattern) (selected : d59058 p = 1) : d60124 p = 1 := by
  have h0 (q : Pattern) (selected : d59041 q = 1) : d59041 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59043 q = 1) : d59043 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d1619 q = 1) : d1619 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d59044 q = 1) : d60115 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59044, d60115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59044, d60115, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro125 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d59045 q = 1) : d60116 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59045, d60116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59045, d60116, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59046 q = 1) : d60117 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59046, d60117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59046, d60117, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59047 q = 1) : d60118 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59047, d60118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59047, d60118, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d59051 q = 1) : d59051 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d59053 q = 1) : d59053 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d1632 q = 1) : d1632 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d59054 q = 1) : d60120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59054, d60120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59054, d60120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro128 q selected
  have h12 (q : Pattern) (selected : d59055 q = 1) : d60121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59055, d60121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d59055, d60121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h13 (q : Pattern) (selected : d59056 q = 1) : d60122 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59056, d60122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d59056, d60122, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d59057 q = 1) : d60123 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59057, d60123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d59057, d60123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d59058 q = 1) : d60124 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59058, d60124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d59058, d60124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1875 (p : Pattern) (selected : d59064 p = 1) : d60130 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1632 q = 1) : d1632 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d59054 q = 1) : d60120 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59054, d60120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59054, d60120, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro128 q selected
  have h3 (q : Pattern) (selected : d59055 q = 1) : d60121 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59055, d60121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59055, d60121, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59062 q = 1) : d60128 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59062, d60128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59062, d60128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59063 q = 1) : d60129 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59063, d60129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59063, d60129, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59064 q = 1) : d60130 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59064, d60130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59064, d60130, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1876 (p : Pattern) (selected : d59073 p = 1) : d60139 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1913 q = 1) : d1913 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d59069 q = 1) : d60135 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59069, d60135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59069, d60135, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro137 q selected
  have h3 (q : Pattern) (selected : d59070 q = 1) : d60136 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59070, d60136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59070, d60136, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59071 q = 1) : d60137 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59071, d60137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59071, d60137, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59072 q = 1) : d60138 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59072, d60138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59072, d60138, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59073 q = 1) : d60139 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59073, d60139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59073, d60139, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1877 (p : Pattern) (selected : d59078 p = 1) : d60144 p = 1 := by
  have h0 (q : Pattern) (selected : d59038 q = 1) : d59038 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59059 q = 1) : d60125 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59059, d60125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1873 q selected
    | true =>
      simp only [d59059, d60125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1874 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d59060 q = 1) : d60126 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59060, d60126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59060, d60126, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59061 q = 1) : d60127 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59061, d60127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59061, d60127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59065 q = 1) : d60131 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59065, d60131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59065, d60131, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1875 q selected
  have h6 (q : Pattern) (selected : d59066 q = 1) : d60132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59066, d60132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59066, d60132, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d59067 q = 1) : d60133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59067, d60133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59067, d60133, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d59068 q = 1) : d60134 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59068, d60134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59068, d60134, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59074 q = 1) : d60140 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59074, d60140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59074, d60140, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1876 q selected
  have h10 (q : Pattern) (selected : d59075 q = 1) : d60141 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59075, d60141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d59075, d60141, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h11 (q : Pattern) (selected : d59076 q = 1) : d60142 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59076, d60142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59076, d60142, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h12 (q : Pattern) (selected : d59077 q = 1) : d60143 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59077, d60143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d59077, d60143, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d59078 q = 1) : d60144 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59078, d60144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d59078, d60144, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro1878 (p : Pattern) (selected : d59084 p = 1) : d60150 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59079 q = 1) : d60145 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59079, d60145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59079, d60145, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1877 q selected
  have h2 (q : Pattern) (selected : d59080 q = 1) : d60146 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59080, d60146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59080, d60146, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d59081 q = 1) : d60147 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59081, d60147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59081, d60147, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59082 q = 1) : d60148 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59082, d60148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59082, d60148, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59083 q = 1) : d60149 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59083, d60149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59083, d60149, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59084 q = 1) : d60150 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59084, d60150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59084, d60150, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1879 (p : Pattern) (selected : d59111 p = 1) : d60159 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59104 q = 1) : d59104 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d59106 q = 1) : d59106 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d2102 q = 1) : d2102 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d59107 q = 1) : d60155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59107, d60155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59107, d60155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h5 (q : Pattern) (selected : d59108 q = 1) : d60156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59108, d60156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59108, d60156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59109 q = 1) : d60157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59109, d60157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59109, d60157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59110 q = 1) : d60158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59110, d60158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59110, d60158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d59111 q = 1) : d60159 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59111, d60159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59111, d60159, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro1880 (p : Pattern) (selected : d59121 p = 1) : d60164 p = 1 := by
  have h0 (q : Pattern) (selected : d59104 q = 1) : d59104 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59106 q = 1) : d59106 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d2102 q = 1) : d2102 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d59107 q = 1) : d60155 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59107, d60155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59107, d60155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro162 q selected
  have h4 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h5 (q : Pattern) (selected : d59108 q = 1) : d60156 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59108, d60156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59108, d60156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59109 q = 1) : d60157 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59109, d60157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59109, d60157, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59110 q = 1) : d60158 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59110, d60158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59110, d60158, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d59114 q = 1) : d59114 q = 1 := by
    exact selected
  have h9 (q : Pattern) (selected : d59116 q = 1) : d59116 q = 1 := by
    exact selected
  have h10 (q : Pattern) (selected : d2115 q = 1) : d2115 q = 1 := by
    exact selected
  have h11 (q : Pattern) (selected : d59117 q = 1) : d60160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59117, d60160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59117, d60160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro165 q selected
  have h12 (q : Pattern) (selected : d59118 q = 1) : d60161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59118, d60161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d59118, d60161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h13 (q : Pattern) (selected : d59119 q = 1) : d60162 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59119, d60162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d59119, d60162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d59120 q = 1) : d60163 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59120, d60163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d59120, d60163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d59121 q = 1) : d60164 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59121, d60164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d59121, d60164, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1881 (p : Pattern) (selected : d59127 p = 1) : d60170 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2115 q = 1) : d2115 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d59117 q = 1) : d60160 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59117, d60160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59117, d60160, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro165 q selected
  have h3 (q : Pattern) (selected : d59118 q = 1) : d60161 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59118, d60161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59118, d60161, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59125 q = 1) : d60168 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59125, d60168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59125, d60168, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59126 q = 1) : d60169 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59126, d60169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59126, d60169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59127 q = 1) : d60170 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59127, d60170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59127, d60170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1882 (p : Pattern) (selected : d59136 p = 1) : d60179 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2391 q = 1) : d2391 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d59132 q = 1) : d60175 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d59132, d60175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59132, d60175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro174 q selected
  have h3 (q : Pattern) (selected : d59133 q = 1) : d60176 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d59133, d60176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59133, d60176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59134 q = 1) : d60177 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d59134, d60177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59134, d60177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59135 q = 1) : d60178 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d59135, d60178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59135, d60178, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59136 q = 1) : d60179 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d59136, d60179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59136, d60179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1883 (p : Pattern) (selected : d59141 p = 1) : d60184 p = 1 := by
  have h0 (q : Pattern) (selected : d59101 q = 1) : d59101 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59122 q = 1) : d60165 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59122, d60165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1879 q selected
    | true =>
      simp only [d59122, d60165, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1880 q selected
  have h2 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d59123 q = 1) : d60166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59123, d60166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59123, d60166, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59124 q = 1) : d60167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59124, d60167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59124, d60167, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59128 q = 1) : d60171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59128, d60171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59128, d60171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1881 q selected
  have h6 (q : Pattern) (selected : d59129 q = 1) : d60172 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59129, d60172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59129, d60172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d59130 q = 1) : d60173 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59130, d60173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59130, d60173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h8 (q : Pattern) (selected : d59131 q = 1) : d60174 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59131, d60174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59131, d60174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59137 q = 1) : d60180 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d59137, d60180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59137, d60180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1882 q selected
  have h10 (q : Pattern) (selected : d59138 q = 1) : d60181 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d59138, d60181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d59138, d60181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h11 (q : Pattern) (selected : d59139 q = 1) : d60182 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59139, d60182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59139, d60182, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h12 (q : Pattern) (selected : d59140 q = 1) : d60183 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d59140, d60183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d59140, d60183, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h13 (q : Pattern) (selected : d59141 q = 1) : d60184 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d59141, d60184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d59141, d60184, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro1884 (p : Pattern) (selected : d59147 p = 1) : d60190 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59142 q = 1) : d60185 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d59142, d60185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59142, d60185, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1883 q selected
  have h2 (q : Pattern) (selected : d59143 q = 1) : d60186 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d59143, d60186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59143, d60186, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d59144 q = 1) : d60187 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d59144, d60187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59144, d60187, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59145 q = 1) : d60188 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d59145, d60188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59145, d60188, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d59146 q = 1) : d60189 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d59146, d60189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59146, d60189, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59147 q = 1) : d60190 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d59147, d60190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59147, d60190, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1885 (p : Pattern) (selected : d59153 p = 1) : d60196 p = 1 := by
  have h0 (q : Pattern) (selected : d58902 q = 1) : d60037 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58902, d60037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1854 q selected
    | true =>
      simp only [d58902, d60037, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1860 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d58962 q = 1) : d60074 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d58962, d60074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d58962, d60074, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1866 q selected
  have h3 (q : Pattern) (selected : d58963 q = 1) : d60075 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d58963, d60075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d58963, d60075, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d59023 q = 1) : d60112 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59023, d60112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59023, d60112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1872 q selected
  have h5 (q : Pattern) (selected : d59024 q = 1) : d60113 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59024, d60113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59024, d60113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d59025 q = 1) : d60114 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59025, d60114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59025, d60114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d59085 q = 1) : d60151 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59085, d60151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59085, d60151, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1878 q selected
  have h8 (q : Pattern) (selected : d59086 q = 1) : d60152 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59086, d60152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59086, d60152, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d59087 q = 1) : d60153 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59087, d60153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59087, d60153, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d59088 q = 1) : d60154 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d59088, d60154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d59088, d60154, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d59148 q = 1) : d60191 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d59148, d60191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59148, d60191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1884 q selected
  have h12 (q : Pattern) (selected : d59149 q = 1) : d60192 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d59149, d60192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59149, d60192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d59150 q = 1) : d60193 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d59150, d60193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59150, d60193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d59151 q = 1) : d60194 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d59151, d60194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59151, d60194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d59152 q = 1) : d60195 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d59152, d60195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d59152, d60195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d59153 q = 1) : d60196 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d59153, d60196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d59153, d60196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1886 (p : Pattern) (selected : d59159 p = 1) : d60202 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59154 q = 1) : d60197 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d59154, d60197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1885 q selected
    | true =>
      simp only [d59154, d60197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59155 q = 1) : d60198 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d59155, d60198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59155, d60198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59156 q = 1) : d60199 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d59156, d60199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59156, d60199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59157 q = 1) : d60200 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d59157, d60200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59157, d60200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59158 q = 1) : d60201 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d59158, d60201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59158, d60201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59159 q = 1) : d60202 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d59159, d60202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59159, d60202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1887 (p : Pattern) (selected : d59165 p = 1) : d60208 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59160 q = 1) : d60203 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d59160, d60203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1886 q selected
    | true =>
      simp only [d59160, d60203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59161 q = 1) : d60204 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d59161, d60204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59161, d60204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59162 q = 1) : d60205 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d59162, d60205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59162, d60205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59163 q = 1) : d60206 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d59163, d60206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59163, d60206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59164 q = 1) : d60207 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d59164, d60207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59164, d60207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59165 q = 1) : d60208 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d59165, d60208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59165, d60208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1888 (p : Pattern) (selected : d59171 p = 1) : d60214 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59166 q = 1) : d60209 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d59166, d60209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1887 q selected
    | true =>
      simp only [d59166, d60209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59167 q = 1) : d60210 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d59167, d60210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59167, d60210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59168 q = 1) : d60211 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d59168, d60211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59168, d60211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59169 q = 1) : d60212 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d59169, d60212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59169, d60212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59170 q = 1) : d60213 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d59170, d60213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59170, d60213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59171 q = 1) : d60214 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d59171, d60214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59171, d60214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1889 (p : Pattern) (selected : d59177 p = 1) : d60220 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59172 q = 1) : d60215 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d59172, d60215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1888 q selected
    | true =>
      simp only [d59172, d60215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59173 q = 1) : d60216 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d59173, d60216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59173, d60216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59174 q = 1) : d60217 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d59174, d60217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59174, d60217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59175 q = 1) : d60218 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d59175, d60218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59175, d60218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59176 q = 1) : d60219 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d59176, d60219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59176, d60219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59177 q = 1) : d60220 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d59177, d60220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59177, d60220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1890 (p : Pattern) (selected : d59183 p = 1) : d60226 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59178 q = 1) : d60221 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d59178, d60221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1889 q selected
    | true =>
      simp only [d59178, d60221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59179 q = 1) : d60222 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d59179, d60222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59179, d60222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59180 q = 1) : d60223 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d59180, d60223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59180, d60223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59181 q = 1) : d60224 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d59181, d60224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59181, d60224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59182 q = 1) : d60225 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d59182, d60225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59182, d60225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59183 q = 1) : d60226 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d59183, d60226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59183, d60226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1891 (p : Pattern) (selected : d59189 p = 1) : d60232 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59184 q = 1) : d60227 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d59184, d60227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1890 q selected
    | true =>
      simp only [d59184, d60227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59185 q = 1) : d60228 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d59185, d60228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59185, d60228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59186 q = 1) : d60229 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d59186, d60229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59186, d60229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59187 q = 1) : d60230 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d59187, d60230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59187, d60230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59188 q = 1) : d60231 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d59188, d60231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59188, d60231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59189 q = 1) : d60232 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d59189, d60232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59189, d60232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1892 (p : Pattern) (selected : d59195 p = 1) : d60238 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d59190 q = 1) : d60233 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d59190, d60233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1891 q selected
    | true =>
      simp only [d59190, d60233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d59191 q = 1) : d60234 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d59191, d60234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d59191, d60234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d59192 q = 1) : d60235 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d59192, d60235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d59192, d60235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59193 q = 1) : d60236 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d59193, d60236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d59193, d60236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d59194 q = 1) : d60237 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d59194, d60237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d59194, d60237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d59195 q = 1) : d60238 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d59195, d60238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d59195, d60238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1893 (p : Pattern) (selected : d64 p = 0) : d51916 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d61 q = 0) : d51913 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, d51913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61, d51913, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro194 q selected
  have h2 (q : Pattern) (selected : d62 q = 0) : d51914 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, d51914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d62, d51914, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d63 q = 0) : d51915 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, d51915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d63, d51915, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d64 q = 0) : d51916 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, d51916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d64, d51916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro1894 (p : Pattern) (selected : d224 p = 0) : d52042 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d221 q = 0) : d52039 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d221, d52039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d221, d52039, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro221 q selected
  have h2 (q : Pattern) (selected : d222 q = 0) : d52040 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222, d52040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222, d52040, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223 q = 0) : d52041 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223, d52041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223, d52041, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d224 q = 0) : d52042 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d224, d52042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d224, d52042, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro1895 (p : Pattern) (selected : d410 p = 0) : d52176 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d405 q = 0) : d52171 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d405, d52171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d405, d52171, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro251 q selected
  have h2 (q : Pattern) (selected : d407 q = 0) : d52173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro252 q selected
  have h3 (q : Pattern) (selected : d408 q = 0) : d52174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d408, d52174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d408, d52174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d409 q = 0) : d52175 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d409, d52175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d409, d52175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d410 q = 0) : d52176 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d410, d52176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d410, d52176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1896 (p : Pattern) (selected : d60256 p = 0) : d60359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60242 q = 0) : d60345 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60242, d60345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60242, d60345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1893 q selected
  have h2 (q : Pattern) (selected : d60243 q = 0) : d60346 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60243, d60346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60243, d60346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60244 q = 0) : d60347 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60244, d60347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60244, d60347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60245 q = 0) : d60348 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60245, d60348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60245, d60348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60246 q = 0) : d60349 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60246, d60349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60246, d60349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1894 q selected
  have h6 (q : Pattern) (selected : d60247 q = 0) : d60350 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60247, d60350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60247, d60350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d60248 q = 0) : d60351 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60248, d60351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60248, d60351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d60249 q = 0) : d60352 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60249, d60352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60249, d60352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d60250 q = 0) : d60353 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60250, d60353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60250, d60353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d60251 q = 0) : d60354 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60251, d60354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60251, d60354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1895 q selected
  have h11 (q : Pattern) (selected : d60252 q = 0) : d60355 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60252, d60355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60252, d60355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d60253 q = 0) : d60356 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60253, d60356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60253, d60356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d60254 q = 0) : d60357 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60254, d60357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60254, d60357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d60255 q = 0) : d60358 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60255, d60358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60255, d60358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d60256 q = 0) : d60359 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60256, d60359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d60256, d60359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1897 (p : Pattern) (selected : d657 p = 0) : d52361 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d652 q = 0) : d52356 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d652, d52356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d652, d52356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro299 q selected
  have h2 (q : Pattern) (selected : d654 q = 0) : d52358 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d654, d52358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro300 q selected
  have h3 (q : Pattern) (selected : d655 q = 0) : d52359 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d655, d52359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d655, d52359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d656 q = 0) : d52360 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d656, d52360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d656, d52360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d657 q = 0) : d52361 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d657, d52361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d657, d52361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1898 (p : Pattern) (selected : d60262 p = 0) : d60365 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60257 q = 0) : d60360 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60257, d60360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60257, d60360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1897 q selected
  have h2 (q : Pattern) (selected : d60258 q = 0) : d60361 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60258, d60361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60258, d60361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60259 q = 0) : d60362 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60259, d60362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60259, d60362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60260 q = 0) : d60363 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60260, d60363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60260, d60363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60261 q = 0) : d60364 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60261, d60364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60261, d60364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60262 q = 0) : d60365 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60262, d60365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60262, d60365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1899 (p : Pattern) (selected : d963 p = 0) : d52582 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d958 q = 0) : d52577 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d958, d52577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d958, d52577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro361 q selected
  have h2 (q : Pattern) (selected : d960 q = 0) : d52579 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d960, d52579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro362 q selected
  have h3 (q : Pattern) (selected : d961 q = 0) : d52580 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d961, d52580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d961, d52580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d962 q = 0) : d52581 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d962, d52581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d962, d52581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d963 q = 0) : d52582 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d963, d52582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d963, d52582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1900 (p : Pattern) (selected : d60269 p = 0) : d60372 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60264 q = 0) : d60367 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60264, d60367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60264, d60367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1899 q selected
  have h2 (q : Pattern) (selected : d60265 q = 0) : d60368 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60265, d60368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60265, d60368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60266 q = 0) : d60369 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60266, d60369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60266, d60369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60267 q = 0) : d60370 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60267, d60370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60267, d60370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60268 q = 0) : d60371 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60268, d60371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60268, d60371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60269 q = 0) : d60372 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60269, d60372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60269, d60372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1901 (p : Pattern) (selected : d1374 p = 0) : d52862 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1369 q = 0) : d52857 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1369, d52857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1369, d52857, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro437 q selected
  have h2 (q : Pattern) (selected : d1371 q = 0) : d52859 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1371, d52859, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro438 q selected
  have h3 (q : Pattern) (selected : d1372 q = 0) : d52860 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1372, d52860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1372, d52860, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1373 q = 0) : d52861 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1373, d52861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1373, d52861, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1374 q = 0) : d52862 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1374, d52862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1374, d52862, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1902 (p : Pattern) (selected : d60277 p = 0) : d60380 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60272 q = 0) : d60375 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60272, d60375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60272, d60375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1901 q selected
  have h2 (q : Pattern) (selected : d60273 q = 0) : d60376 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60273, d60376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60273, d60376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60274 q = 0) : d60377 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60274, d60377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60274, d60377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60275 q = 0) : d60378 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60275, d60378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60275, d60378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60276 q = 0) : d60379 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60276, d60379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60276, d60379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60277 q = 0) : d60380 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60277, d60380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60277, d60380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1903 (p : Pattern) (selected : d1851 p = 0) : d53177 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1846 q = 0) : d53172 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1846, d53172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1846, d53172, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro523 q selected
  have h2 (q : Pattern) (selected : d1848 q = 0) : d53174 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1848, d53174, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro524 q selected
  have h3 (q : Pattern) (selected : d1849 q = 0) : d53175 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1849, d53175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1849, d53175, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1850 q = 0) : d53176 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1850, d53176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1850, d53176, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1851 q = 0) : d53177 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1851, d53177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1851, d53177, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1904 (p : Pattern) (selected : d60286 p = 0) : d60389 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60281 q = 0) : d60384 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60281, d60384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60281, d60384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1903 q selected
  have h2 (q : Pattern) (selected : d60282 q = 0) : d60385 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60282, d60385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60282, d60385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60283 q = 0) : d60386 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60283, d60386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60283, d60386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60284 q = 0) : d60387 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60284, d60387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60284, d60387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60285 q = 0) : d60388 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60285, d60388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60285, d60388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60286 q = 0) : d60389 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60286, d60389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60286, d60389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1905 (p : Pattern) (selected : d2329 p = 0) : d53494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2324 q = 0) : d53489 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2324, d53489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2324, d53489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro613 q selected
  have h2 (q : Pattern) (selected : d2326 q = 0) : d53491 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2326, d53491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro614 q selected
  have h3 (q : Pattern) (selected : d2327 q = 0) : d53492 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2327, d53492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2327, d53492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2328 q = 0) : d53493 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2328, d53493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2328, d53493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2329 q = 0) : d53494 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2329, d53494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2329, d53494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1906 (p : Pattern) (selected : d60296 p = 0) : d60399 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60291 q = 0) : d60394 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60291, d60394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60291, d60394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1905 q selected
  have h2 (q : Pattern) (selected : d60292 q = 0) : d60395 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60292, d60395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60292, d60395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60293 q = 0) : d60396 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60293, d60396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60293, d60396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60294 q = 0) : d60397 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60294, d60397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60294, d60397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60295 q = 0) : d60398 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60295, d60398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60295, d60398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60296 q = 0) : d60399 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60296, d60399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60296, d60399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1907 (p : Pattern) (selected : d60302 p = 0) : d60405 p = 1 := by
  have h0 (q : Pattern) (selected : d60263 q = 0) : d60366 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60263, d60366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1896 q selected
    | true =>
      simp only [d60263, d60366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1898 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d60270 q = 0) : d60373 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60270, d60373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60270, d60373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1900 q selected
  have h3 (q : Pattern) (selected : d60271 q = 0) : d60374 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60271, d60374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60271, d60374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60278 q = 0) : d60381 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60278, d60381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60278, d60381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1902 q selected
  have h5 (q : Pattern) (selected : d60279 q = 0) : d60382 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60279, d60382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60279, d60382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60280 q = 0) : d60383 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60280, d60383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60280, d60383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d60287 q = 0) : d60390 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60287, d60390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60287, d60390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1904 q selected
  have h8 (q : Pattern) (selected : d60288 q = 0) : d60391 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60288, d60391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60288, d60391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d60289 q = 0) : d60392 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60289, d60392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60289, d60392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d60290 q = 0) : d60393 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d60290, d60393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d60290, d60393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d60297 q = 0) : d60400 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60297, d60400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60297, d60400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1906 q selected
  have h12 (q : Pattern) (selected : d60298 q = 0) : d60401 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60298, d60401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60298, d60401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d60299 q = 0) : d60402 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60299, d60402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60299, d60402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d60300 q = 0) : d60403 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d60300, d60403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60300, d60403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d60301 q = 0) : d60404 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d60301, d60404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d60301, d60404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d60302 q = 0) : d60405 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d60302, d60405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d60302, d60405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1908 (p : Pattern) (selected : d60308 p = 0) : d60411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60303 q = 0) : d60406 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d60303, d60406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1907 q selected
    | true =>
      simp only [d60303, d60406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60304 q = 0) : d60407 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d60304, d60407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60304, d60407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60305 q = 0) : d60408 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d60305, d60408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60305, d60408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60306 q = 0) : d60409 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d60306, d60409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60306, d60409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60307 q = 0) : d60410 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d60307, d60410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60307, d60410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60308 q = 0) : d60411 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d60308, d60411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60308, d60411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1909 (p : Pattern) (selected : d60314 p = 0) : d60417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60309 q = 0) : d60412 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d60309, d60412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1908 q selected
    | true =>
      simp only [d60309, d60412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60310 q = 0) : d60413 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d60310, d60413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60310, d60413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60311 q = 0) : d60414 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d60311, d60414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60311, d60414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60312 q = 0) : d60415 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d60312, d60415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60312, d60415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60313 q = 0) : d60416 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d60313, d60416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60313, d60416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60314 q = 0) : d60417 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d60314, d60417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60314, d60417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1910 (p : Pattern) (selected : d60320 p = 0) : d60423 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60315 q = 0) : d60418 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d60315, d60418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1909 q selected
    | true =>
      simp only [d60315, d60418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60316 q = 0) : d60419 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d60316, d60419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60316, d60419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60317 q = 0) : d60420 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d60317, d60420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60317, d60420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60318 q = 0) : d60421 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d60318, d60421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60318, d60421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60319 q = 0) : d60422 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d60319, d60422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60319, d60422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60320 q = 0) : d60423 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d60320, d60423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60320, d60423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1911 (p : Pattern) (selected : d60326 p = 0) : d60429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60321 q = 0) : d60424 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d60321, d60424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1910 q selected
    | true =>
      simp only [d60321, d60424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60322 q = 0) : d60425 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d60322, d60425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60322, d60425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60323 q = 0) : d60426 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d60323, d60426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60323, d60426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60324 q = 0) : d60427 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d60324, d60427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60324, d60427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60325 q = 0) : d60428 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d60325, d60428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60325, d60428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60326 q = 0) : d60429 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d60326, d60429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60326, d60429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1912 (p : Pattern) (selected : d60332 p = 0) : d60435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60327 q = 0) : d60430 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d60327, d60430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1911 q selected
    | true =>
      simp only [d60327, d60430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60328 q = 0) : d60431 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d60328, d60431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60328, d60431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60329 q = 0) : d60432 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d60329, d60432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60329, d60432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60330 q = 0) : d60433 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d60330, d60433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60330, d60433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60331 q = 0) : d60434 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d60331, d60434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60331, d60434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60332 q = 0) : d60435 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d60332, d60435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60332, d60435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1913 (p : Pattern) (selected : d60338 p = 0) : d60441 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60333 q = 0) : d60436 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d60333, d60436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1912 q selected
    | true =>
      simp only [d60333, d60436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60334 q = 0) : d60437 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d60334, d60437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60334, d60437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60335 q = 0) : d60438 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d60335, d60438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60335, d60438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60336 q = 0) : d60439 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d60336, d60439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60336, d60439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60337 q = 0) : d60440 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d60337, d60440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60337, d60440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60338 q = 0) : d60441 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d60338, d60441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60338, d60441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1914 (p : Pattern) (selected : d60344 p = 0) : d60447 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d60339 q = 0) : d60442 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d60339, d60442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1913 q selected
    | true =>
      simp only [d60339, d60442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60340 q = 0) : d60443 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d60340, d60443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60340, d60443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60341 q = 0) : d60444 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d60341, d60444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60341, d60444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60342 q = 0) : d60445 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d60342, d60445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60342, d60445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60343 q = 0) : d60446 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d60343, d60446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60343, d60446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60344 q = 0) : d60447 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d60344, d60447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60344, d60447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1915 (p : Pattern) (selected : d224 p = 1) : d4353 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d221 q = 1) : d4350 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d221, d4350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d221, d4350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro8 q selected
  have h2 (q : Pattern) (selected : d222 q = 1) : d4351 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222, d4351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d222, d4351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d223 q = 1) : d4352 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223, d4352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d223, d4352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d224 q = 1) : d4353 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d224, d4353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d224, d4353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h4 p selected
theorem eqIntro1916 (p : Pattern) (selected : d410 p = 1) : d51670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d405 q = 1) : d4386 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d405, d4386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d405, d4386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro22 q selected
  have h2 (q : Pattern) (selected : d407 q = 1) : d407 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d408 q = 1) : d51668 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d408, d51668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d408, d51668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d409 q = 1) : d51669 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d409, d51669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d409, d51669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d410 q = 1) : d51670 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d410, d51670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d410, d51670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1917 (p : Pattern) (selected : d60256 p = 1) : d61264 p = 1 := by
  have h0 (q : Pattern) (selected : d60245 q = 1) : d60245 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d60246 q = 1) : d61254 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60246, d61254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60246, d61254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1915 q selected
  have h3 (q : Pattern) (selected : d60247 q = 1) : d61255 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60247, d61255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60247, d61255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60248 q = 1) : d61256 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60248, d61256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60248, d61256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60249 q = 1) : d61257 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60249, d61257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60249, d61257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60250 q = 1) : d61258 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60250, d61258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60250, d61258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d60251 q = 1) : d61259 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60251, d61259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60251, d61259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1916 q selected
  have h8 (q : Pattern) (selected : d60252 q = 1) : d61260 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60252, d61260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60252, d61260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d60253 q = 1) : d61261 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60253, d61261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60253, d61261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d60254 q = 1) : d61262 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60254, d61262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60254, d61262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d60255 q = 1) : d61263 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60255, d61263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60255, d61263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d60256 q = 1) : d61264 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60256, d61264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d60256, d61264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro1918 (p : Pattern) (selected : d657 p = 1) : d51695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d652 q = 1) : d4423 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d652, d4423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d652, d4423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro40 q selected
  have h2 (q : Pattern) (selected : d654 q = 1) : d654 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d655 q = 1) : d51693 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d655, d51693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d655, d51693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d656 q = 1) : d51694 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d656, d51694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d656, d51694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d657 q = 1) : d51695 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d657, d51695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d657, d51695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1919 (p : Pattern) (selected : d60262 p = 1) : d61270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60257 q = 1) : d61265 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60257, d61265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60257, d61265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1918 q selected
  have h2 (q : Pattern) (selected : d60258 q = 1) : d61266 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60258, d61266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60258, d61266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60259 q = 1) : d61267 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60259, d61267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60259, d61267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60260 q = 1) : d61268 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60260, d61268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60260, d61268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60261 q = 1) : d61269 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60261, d61269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60261, d61269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60262 q = 1) : d61270 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60262, d61270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60262, d61270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1920 (p : Pattern) (selected : d963 p = 1) : d51721 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d958 q = 1) : d4461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d958, d4461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d958, d4461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro64 q selected
  have h2 (q : Pattern) (selected : d960 q = 1) : d960 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d961 q = 1) : d51719 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d961, d51719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d961, d51719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d962 q = 1) : d51720 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d962, d51720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d962, d51720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d963 q = 1) : d51721 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d963, d51721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d963, d51721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1921 (p : Pattern) (selected : d60269 p = 1) : d61277 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60264 q = 1) : d61272 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60264, d61272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60264, d61272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1920 q selected
  have h2 (q : Pattern) (selected : d60265 q = 1) : d61273 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60265, d61273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60265, d61273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60266 q = 1) : d61274 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60266, d61274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60266, d61274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60267 q = 1) : d61275 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60267, d61275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60267, d61275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60268 q = 1) : d61276 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60268, d61276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60268, d61276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60269 q = 1) : d61277 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60269, d61277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60269, d61277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1922 (p : Pattern) (selected : d1374 p = 1) : d51748 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1369 q = 1) : d4500 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1369, d4500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1369, d4500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro94 q selected
  have h2 (q : Pattern) (selected : d1371 q = 1) : d1371 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1372 q = 1) : d51746 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1372, d51746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1372, d51746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1373 q = 1) : d51747 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1373, d51747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1373, d51747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1374 q = 1) : d51748 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1374, d51748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1374, d51748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1923 (p : Pattern) (selected : d60277 p = 1) : d61285 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60272 q = 1) : d61280 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60272, d61280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60272, d61280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1922 q selected
  have h2 (q : Pattern) (selected : d60273 q = 1) : d61281 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60273, d61281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60273, d61281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60274 q = 1) : d61282 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60274, d61282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60274, d61282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60275 q = 1) : d61283 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60275, d61283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60275, d61283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60276 q = 1) : d61284 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60276, d61284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60276, d61284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60277 q = 1) : d61285 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60277, d61285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60277, d61285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1924 (p : Pattern) (selected : d1851 p = 1) : d51776 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d1846 q = 1) : d4540 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1846, d4540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1846, d4540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro130 q selected
  have h2 (q : Pattern) (selected : d1848 q = 1) : d1848 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d1849 q = 1) : d51774 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1849, d51774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1849, d51774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d1850 q = 1) : d51775 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1850, d51775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1850, d51775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1851 q = 1) : d51776 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1851, d51776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d1851, d51776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1925 (p : Pattern) (selected : d60286 p = 1) : d61294 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60281 q = 1) : d61289 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60281, d61289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60281, d61289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1924 q selected
  have h2 (q : Pattern) (selected : d60282 q = 1) : d61290 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60282, d61290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60282, d61290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60283 q = 1) : d61291 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60283, d61291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60283, d61291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60284 q = 1) : d61292 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60284, d61292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60284, d61292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60285 q = 1) : d61293 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60285, d61293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60285, d61293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60286 q = 1) : d61294 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60286, d61294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60286, d61294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1926 (p : Pattern) (selected : d2329 p = 1) : d51805 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d2324 q = 1) : d4581 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2324, d4581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2324, d4581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro167 q selected
  have h2 (q : Pattern) (selected : d2326 q = 1) : d2326 q = 1 := by
    exact selected
  have h3 (q : Pattern) (selected : d2327 q = 1) : d51803 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2327, d51803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2327, d51803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2328 q = 1) : d51804 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2328, d51804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2328, d51804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2329 q = 1) : d51805 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2329, d51805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2329, d51805, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h5 p selected
theorem eqIntro1927 (p : Pattern) (selected : d60296 p = 1) : d61304 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60291 q = 1) : d61299 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d60291, d61299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60291, d61299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1926 q selected
  have h2 (q : Pattern) (selected : d60292 q = 1) : d61300 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d60292, d61300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60292, d61300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d60293 q = 1) : d61301 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d60293, d61301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60293, d61301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60294 q = 1) : d61302 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d60294, d61302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60294, d61302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d60295 q = 1) : d61303 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d60295, d61303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60295, d61303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60296 q = 1) : d61304 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d60296, d61304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60296, d61304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1928 (p : Pattern) (selected : d60302 p = 1) : d61310 p = 1 := by
  have h0 (q : Pattern) (selected : d60263 q = 1) : d61271 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60263, d61271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1917 q selected
    | true =>
      simp only [d60263, d61271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1919 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d60270 q = 1) : d61278 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60270, d61278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60270, d61278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1921 q selected
  have h3 (q : Pattern) (selected : d60271 q = 1) : d61279 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60271, d61279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d60271, d61279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d60278 q = 1) : d61286 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60278, d61286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60278, d61286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1923 q selected
  have h5 (q : Pattern) (selected : d60279 q = 1) : d61287 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60279, d61287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60279, d61287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d60280 q = 1) : d61288 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60280, d61288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60280, d61288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d60287 q = 1) : d61295 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60287, d61295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60287, d61295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1925 q selected
  have h8 (q : Pattern) (selected : d60288 q = 1) : d61296 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60288, d61296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60288, d61296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d60289 q = 1) : d61297 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60289, d61297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60289, d61297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d60290 q = 1) : d61298 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d60290, d61298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d60290, d61298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d60297 q = 1) : d61305 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d60297, d61305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60297, d61305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1927 q selected
  have h12 (q : Pattern) (selected : d60298 q = 1) : d61306 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d60298, d61306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60298, d61306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d60299 q = 1) : d61307 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d60299, d61307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60299, d61307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d60300 q = 1) : d61308 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d60300, d61308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60300, d61308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d60301 q = 1) : d61309 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d60301, d61309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d60301, d61309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d60302 q = 1) : d61310 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d60302, d61310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d60302, d61310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1929 (p : Pattern) (selected : d60308 p = 1) : d61316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60303 q = 1) : d61311 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d60303, d61311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1928 q selected
    | true =>
      simp only [d60303, d61311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60304 q = 1) : d61312 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d60304, d61312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60304, d61312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60305 q = 1) : d61313 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d60305, d61313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60305, d61313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60306 q = 1) : d61314 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d60306, d61314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60306, d61314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60307 q = 1) : d61315 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d60307, d61315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60307, d61315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60308 q = 1) : d61316 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d60308, d61316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60308, d61316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1930 (p : Pattern) (selected : d60314 p = 1) : d61322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60309 q = 1) : d61317 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d60309, d61317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1929 q selected
    | true =>
      simp only [d60309, d61317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60310 q = 1) : d61318 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d60310, d61318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60310, d61318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60311 q = 1) : d61319 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d60311, d61319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60311, d61319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60312 q = 1) : d61320 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d60312, d61320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60312, d61320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60313 q = 1) : d61321 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d60313, d61321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60313, d61321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60314 q = 1) : d61322 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d60314, d61322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60314, d61322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1931 (p : Pattern) (selected : d60320 p = 1) : d61328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60315 q = 1) : d61323 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d60315, d61323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1930 q selected
    | true =>
      simp only [d60315, d61323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60316 q = 1) : d61324 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d60316, d61324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60316, d61324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60317 q = 1) : d61325 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d60317, d61325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60317, d61325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60318 q = 1) : d61326 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d60318, d61326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60318, d61326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60319 q = 1) : d61327 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d60319, d61327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60319, d61327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60320 q = 1) : d61328 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d60320, d61328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60320, d61328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1932 (p : Pattern) (selected : d60326 p = 1) : d61334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60321 q = 1) : d61329 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d60321, d61329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1931 q selected
    | true =>
      simp only [d60321, d61329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60322 q = 1) : d61330 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d60322, d61330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60322, d61330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60323 q = 1) : d61331 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d60323, d61331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60323, d61331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60324 q = 1) : d61332 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d60324, d61332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60324, d61332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60325 q = 1) : d61333 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d60325, d61333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60325, d61333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60326 q = 1) : d61334 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d60326, d61334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60326, d61334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1933 (p : Pattern) (selected : d60332 p = 1) : d61340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60327 q = 1) : d61335 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d60327, d61335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1932 q selected
    | true =>
      simp only [d60327, d61335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60328 q = 1) : d61336 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d60328, d61336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60328, d61336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60329 q = 1) : d61337 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d60329, d61337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60329, d61337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60330 q = 1) : d61338 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d60330, d61338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60330, d61338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60331 q = 1) : d61339 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d60331, d61339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60331, d61339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60332 q = 1) : d61340 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d60332, d61340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60332, d61340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1934 (p : Pattern) (selected : d60338 p = 1) : d61346 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60333 q = 1) : d61341 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d60333, d61341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1933 q selected
    | true =>
      simp only [d60333, d61341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60334 q = 1) : d61342 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d60334, d61342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60334, d61342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60335 q = 1) : d61343 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d60335, d61343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60335, d61343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60336 q = 1) : d61344 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d60336, d61344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60336, d61344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60337 q = 1) : d61345 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d60337, d61345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60337, d61345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60338 q = 1) : d61346 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d60338, d61346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60338, d61346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1935 (p : Pattern) (selected : d60344 p = 1) : d61352 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d60339 q = 1) : d61347 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d60339, d61347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1934 q selected
    | true =>
      simp only [d60339, d61347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d60340 q = 1) : d61348 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d60340, d61348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d60340, d61348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d60341 q = 1) : d61349 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d60341, d61349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d60341, d61349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d60342 q = 1) : d61350 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d60342, d61350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d60342, d61350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d60343 q = 1) : d61351 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d60343, d61351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d60343, d61351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d60344 q = 1) : d61352 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d60344, d61352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d60344, d61352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1936 (p : Pattern) (selected : d3324 p = 0) : d61366 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3319 q = 0) : d61361 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3319, d61361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro191 q selected
    | true =>
      simp only [d3319, d61361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3320 q = 0) : d61362 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3320, d61362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3320, d61362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3321 q = 0) : d61363 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3321, d61363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3321, d61363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3322 q = 0) : d61364 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3322, d61364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3322, d61364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3323 q = 0) : d61365 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3323, d61365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3323, d61365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3324 q = 0) : d61366 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3324, d61366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3324, d61366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1937 (p : Pattern) (selected : d3337 p = 0) : d61379 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3329 q = 0) : d61371 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3329, d61371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro200 q selected
    | true =>
      simp only [d3329, d61371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3330 q = 0) : d61372 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3330, d61372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3330, d61372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3331 q = 0) : d61373 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3331, d61373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3331, d61373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3332 q = 0) : d61374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3332, d61374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro214 q selected
    | true =>
      simp only [d3332, d61374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d214 q = 0) : d52032 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro220 q selected
    | true =>
      simp only [d214, d52032, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3333 q = 0) : d61375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3333, d61375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3333, d61375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3334 q = 0) : d61376 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3334, d61376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3334, d61376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3335 q = 0) : d61377 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3335, d61377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3335, d61377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3336 q = 0) : d61378 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3336, d61378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3336, d61378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3337 q = 0) : d61379 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3337, d61379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3337, d61379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro1938 (p : Pattern) (selected : d3352 p = 0) : d61394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3343 q = 0) : d61385 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3343, d61385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro230 q selected
    | true =>
      simp only [d3343, d61385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3344 q = 0) : d61386 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3344, d61386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3344, d61386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3345 q = 0) : d61387 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3345, d61387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3345, d61387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3346 q = 0) : d61388 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3346, d61388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro244 q selected
    | true =>
      simp only [d3346, d61388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3347 q = 0) : d61389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3347, d61389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro250 q selected
    | true =>
      simp only [d3347, d61389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3348 q = 0) : d61390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3348, d61390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3348, d61390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3349 q = 0) : d61391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3349, d61391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3349, d61391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3350 q = 0) : d61392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3350, d61392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3350, d61392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3351 q = 0) : d61393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3351, d61393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3351, d61393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3352 q = 0) : d61394 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3352, d61394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3352, d61394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro1939 (p : Pattern) (selected : d3358 p = 0) : d61400 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3325 q = 0) : d61367 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3325, d61367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3325, d61367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1936 q selected
  have h2 (q : Pattern) (selected : d3326 q = 0) : d61368 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3326, d61368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3326, d61368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3327 q = 0) : d61369 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3327, d61369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3327, d61369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3328 q = 0) : d61370 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3328, d61370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3328, d61370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3338 q = 0) : d61380 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3338, d61380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3338, d61380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1937 q selected
  have h6 (q : Pattern) (selected : d3339 q = 0) : d61381 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3339, d61381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3339, d61381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3340 q = 0) : d61382 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3340, d61382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3340, d61382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d3341 q = 0) : d61383 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3341, d61383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3341, d61383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3342 q = 0) : d61384 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3342, d61384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3342, d61384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3353 q = 0) : d61395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3353, d61395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3353, d61395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1938 q selected
  have h11 (q : Pattern) (selected : d3354 q = 0) : d61396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3354, d61396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3354, d61396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3355 q = 0) : d61397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3355, d61397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3355, d61397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3356 q = 0) : d61398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3356, d61398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3356, d61398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3357 q = 0) : d61399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3357, d61399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3357, d61399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3358 q = 0) : d61400 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3358, d61400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3358, d61400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1940 (p : Pattern) (selected : d3368 p = 0) : d61410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3359 q = 0) : d61401 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3359, d61401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro267 q selected
    | true =>
      simp only [d3359, d61401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3360 q = 0) : d61402 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3360, d61402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3360, d61402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3361 q = 0) : d61403 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3361, d61403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3361, d61403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3362 q = 0) : d61404 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3362, d61404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro288 q selected
    | true =>
      simp only [d3362, d61404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3363 q = 0) : d61405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3363, d61405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro297 q selected
    | true =>
      simp only [d3363, d61405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3364 q = 0) : d61406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3364, d61406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3364, d61406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3365 q = 0) : d61407 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3365, d61407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3365, d61407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3366 q = 0) : d61408 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3366, d61408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3366, d61408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3367 q = 0) : d61409 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3367, d61409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3367, d61409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3368 q = 0) : d61410 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3368, d61410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3368, d61410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro1941 (p : Pattern) (selected : d3374 p = 0) : d61416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3369 q = 0) : d61411 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3369, d61411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3369, d61411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1940 q selected
  have h2 (q : Pattern) (selected : d3370 q = 0) : d61412 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3370, d61412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3370, d61412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3371 q = 0) : d61413 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3371, d61413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3371, d61413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3372 q = 0) : d61414 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3372, d61414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3372, d61414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3373 q = 0) : d61415 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3373, d61415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3373, d61415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3374 q = 0) : d61416 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3374, d61416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3374, d61416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1942 (p : Pattern) (selected : d3385 p = 0) : d61427 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3376 q = 0) : d61418 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3376, d61418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro325 q selected
    | true =>
      simp only [d3376, d61418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3377 q = 0) : d61419 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3377, d61419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3377, d61419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3378 q = 0) : d61420 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3378, d61420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3378, d61420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3379 q = 0) : d61421 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3379, d61421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro350 q selected
    | true =>
      simp only [d3379, d61421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3380 q = 0) : d61422 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3380, d61422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro359 q selected
    | true =>
      simp only [d3380, d61422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3381 q = 0) : d61423 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3381, d61423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3381, d61423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3382 q = 0) : d61424 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3382, d61424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3382, d61424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3383 q = 0) : d61425 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3383, d61425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3383, d61425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3384 q = 0) : d61426 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3384, d61426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3384, d61426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3385 q = 0) : d61427 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3385, d61427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3385, d61427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro1943 (p : Pattern) (selected : d3391 p = 0) : d61433 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3386 q = 0) : d61428 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3386, d61428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3386, d61428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1942 q selected
  have h2 (q : Pattern) (selected : d3387 q = 0) : d61429 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3387, d61429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3387, d61429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3388 q = 0) : d61430 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3388, d61430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3388, d61430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3389 q = 0) : d61431 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3389, d61431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3389, d61431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3390 q = 0) : d61432 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3390, d61432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3390, d61432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3391 q = 0) : d61433 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3391, d61433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3391, d61433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1944 (p : Pattern) (selected : d3403 p = 0) : d61445 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3394 q = 0) : d61436 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3394, d61436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro397 q selected
    | true =>
      simp only [d3394, d61436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3395 q = 0) : d61437 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3395, d61437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3395, d61437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3396 q = 0) : d61438 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3396, d61438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3396, d61438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3397 q = 0) : d61439 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3397, d61439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro426 q selected
    | true =>
      simp only [d3397, d61439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3398 q = 0) : d61440 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3398, d61440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro435 q selected
    | true =>
      simp only [d3398, d61440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3399 q = 0) : d61441 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3399, d61441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3399, d61441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3400 q = 0) : d61442 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3400, d61442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3400, d61442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3401 q = 0) : d61443 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3401, d61443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3401, d61443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3402 q = 0) : d61444 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3402, d61444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3402, d61444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3403 q = 0) : d61445 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3403, d61445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3403, d61445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro1945 (p : Pattern) (selected : d3409 p = 0) : d61451 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3404 q = 0) : d61446 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3404, d61446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3404, d61446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1944 q selected
  have h2 (q : Pattern) (selected : d3405 q = 0) : d61447 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3405, d61447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3405, d61447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3406 q = 0) : d61448 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3406, d61448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3406, d61448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3407 q = 0) : d61449 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3407, d61449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3407, d61449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3408 q = 0) : d61450 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3408, d61450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3408, d61450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3409 q = 0) : d61451 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3409, d61451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3409, d61451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1946 (p : Pattern) (selected : d3422 p = 0) : d61464 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3413 q = 0) : d61455 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3413, d61455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro479 q selected
    | true =>
      simp only [d3413, d61455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3414 q = 0) : d61456 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3414, d61456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3414, d61456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3415 q = 0) : d61457 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3415, d61457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3415, d61457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3416 q = 0) : d61458 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3416, d61458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro512 q selected
    | true =>
      simp only [d3416, d61458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3417 q = 0) : d61459 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3417, d61459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro521 q selected
    | true =>
      simp only [d3417, d61459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3418 q = 0) : d61460 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3418, d61460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3418, d61460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3419 q = 0) : d61461 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3419, d61461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3419, d61461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3420 q = 0) : d61462 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3420, d61462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3420, d61462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3421 q = 0) : d61463 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3421, d61463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3421, d61463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3422 q = 0) : d61464 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3422, d61464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3422, d61464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro1947 (p : Pattern) (selected : d3428 p = 0) : d61470 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3423 q = 0) : d61465 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3423, d61465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3423, d61465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1946 q selected
  have h2 (q : Pattern) (selected : d3424 q = 0) : d61466 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3424, d61466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3424, d61466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3425 q = 0) : d61467 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3425, d61467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3425, d61467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3426 q = 0) : d61468 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3426, d61468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3426, d61468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3427 q = 0) : d61469 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3427, d61469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3427, d61469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3428 q = 0) : d61470 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3428, d61470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3428, d61470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1948 (p : Pattern) (selected : d3442 p = 0) : d61484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3433 q = 0) : d61475 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3433, d61475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro568 q selected
    | true =>
      simp only [d3433, d61475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3434 q = 0) : d61476 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3434, d61476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3434, d61476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3435 q = 0) : d61477 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3435, d61477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3435, d61477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3436 q = 0) : d61478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3436, d61478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro602 q selected
    | true =>
      simp only [d3436, d61478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3437 q = 0) : d61479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3437, d61479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro611 q selected
    | true =>
      simp only [d3437, d61479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3438 q = 0) : d61480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3438, d61480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3438, d61480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3439 q = 0) : d61481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3439, d61481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3439, d61481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d3440 q = 0) : d61482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3440, d61482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3440, d61482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3441 q = 0) : d61483 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3441, d61483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d3441, d61483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d3442 q = 0) : d61484 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3442, d61484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d3442, d61484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro1949 (p : Pattern) (selected : d3448 p = 0) : d61490 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3443 q = 0) : d61485 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3443, d61485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3443, d61485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1948 q selected
  have h2 (q : Pattern) (selected : d3444 q = 0) : d61486 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3444, d61486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3444, d61486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3445 q = 0) : d61487 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3445, d61487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3445, d61487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3446 q = 0) : d61488 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3446, d61488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3446, d61488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3447 q = 0) : d61489 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3447, d61489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3447, d61489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3448 q = 0) : d61490 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3448, d61490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3448, d61490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1950 (p : Pattern) (selected : d3454 p = 0) : d61496 p = 1 := by
  have h0 (q : Pattern) (selected : d3375 q = 0) : d61417 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3375, d61417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1939 q selected
    | true =>
      simp only [d3375, d61417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1941 q selected
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d3392 q = 0) : d61434 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3392, d61434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3392, d61434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1943 q selected
  have h3 (q : Pattern) (selected : d3393 q = 0) : d61435 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3393, d61435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3393, d61435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3410 q = 0) : d61452 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3410, d61452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3410, d61452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1945 q selected
  have h5 (q : Pattern) (selected : d3411 q = 0) : d61453 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3411, d61453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3411, d61453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3412 q = 0) : d61454 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3412, d61454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3412, d61454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3429 q = 0) : d61471 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3429, d61471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3429, d61471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1947 q selected
  have h8 (q : Pattern) (selected : d3430 q = 0) : d61472 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3430, d61472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3430, d61472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3431 q = 0) : d61473 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3431, d61473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3431, d61473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3432 q = 0) : d61474 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3432, d61474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3432, d61474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3449 q = 0) : d61491 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3449, d61491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3449, d61491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1949 q selected
  have h12 (q : Pattern) (selected : d3450 q = 0) : d61492 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3450, d61492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3450, d61492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3451 q = 0) : d61493 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3451, d61493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3451, d61493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3452 q = 0) : d61494 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3452, d61494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3452, d61494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3453 q = 0) : d61495 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3453, d61495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3453, d61495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3454 q = 0) : d61496 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3454, d61496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3454, d61496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1951 (p : Pattern) (selected : d3460 p = 0) : d61502 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3455 q = 0) : d61497 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3455, d61497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1950 q selected
    | true =>
      simp only [d3455, d61497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3456 q = 0) : d61498 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3456, d61498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3456, d61498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3457 q = 0) : d61499 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3457, d61499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3457, d61499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3458 q = 0) : d61500 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3458, d61500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3458, d61500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3459 q = 0) : d61501 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3459, d61501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3459, d61501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3460 q = 0) : d61502 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3460, d61502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3460, d61502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1952 (p : Pattern) (selected : d3466 p = 0) : d61508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3461 q = 0) : d61503 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3461, d61503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1951 q selected
    | true =>
      simp only [d3461, d61503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3462 q = 0) : d61504 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3462, d61504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3462, d61504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3463 q = 0) : d61505 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3463, d61505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3463, d61505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3464 q = 0) : d61506 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3464, d61506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3464, d61506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3465 q = 0) : d61507 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3465, d61507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3465, d61507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3466 q = 0) : d61508 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3466, d61508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3466, d61508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1953 (p : Pattern) (selected : d3472 p = 0) : d61514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3467 q = 0) : d61509 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3467, d61509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1952 q selected
    | true =>
      simp only [d3467, d61509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3468 q = 0) : d61510 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3468, d61510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3468, d61510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3469 q = 0) : d61511 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3469, d61511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3469, d61511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3470 q = 0) : d61512 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3470, d61512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3470, d61512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3471 q = 0) : d61513 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3471, d61513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3471, d61513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3472 q = 0) : d61514 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3472, d61514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3472, d61514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1954 (p : Pattern) (selected : d3478 p = 0) : d61520 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3473 q = 0) : d61515 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3473, d61515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1953 q selected
    | true =>
      simp only [d3473, d61515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3474 q = 0) : d61516 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3474, d61516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3474, d61516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3475 q = 0) : d61517 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3475, d61517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3475, d61517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3476 q = 0) : d61518 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3476, d61518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3476, d61518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3477 q = 0) : d61519 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3477, d61519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3477, d61519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3478 q = 0) : d61520 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3478, d61520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3478, d61520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1955 (p : Pattern) (selected : d3484 p = 0) : d61526 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3479 q = 0) : d61521 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3479, d61521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1954 q selected
    | true =>
      simp only [d3479, d61521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3480 q = 0) : d61522 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3480, d61522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3480, d61522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3481 q = 0) : d61523 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3481, d61523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3481, d61523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3482 q = 0) : d61524 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3482, d61524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3482, d61524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3483 q = 0) : d61525 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3483, d61525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3483, d61525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3484 q = 0) : d61526 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3484, d61526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3484, d61526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1956 (p : Pattern) (selected : d3490 p = 0) : d61532 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3485 q = 0) : d61527 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3485, d61527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1955 q selected
    | true =>
      simp only [d3485, d61527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3486 q = 0) : d61528 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3486, d61528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3486, d61528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3487 q = 0) : d61529 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3487, d61529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3487, d61529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3488 q = 0) : d61530 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3488, d61530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3488, d61530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3489 q = 0) : d61531 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3489, d61531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3489, d61531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3490 q = 0) : d61532 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3490, d61532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3490, d61532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1957 (p : Pattern) (selected : d3496 p = 0) : d61538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d3491 q = 0) : d61533 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3491, d61533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1956 q selected
    | true =>
      simp only [d3491, d61533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3492 q = 0) : d61534 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3492, d61534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3492, d61534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3493 q = 0) : d61535 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3493, d61535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3493, d61535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3494 q = 0) : d61536 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3494, d61536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3494, d61536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3495 q = 0) : d61537 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3495, d61537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3495, d61537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3496 q = 0) : d61538 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3496, d61538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3496, d61538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1958 (p : Pattern) (selected : d3337 p = 1) : d61544 p = 1 := by
  have h0 (q : Pattern) (selected : d3331 q = 1) : d3331 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3332 q = 1) : d61539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3332, d61539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro5 q selected
    | true =>
      simp only [d3332, d61539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d214 q = 1) : d214 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3333 q = 1) : d61540 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3333, d61540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3333, d61540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3334 q = 1) : d61541 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3334, d61541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3334, d61541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3335 q = 1) : d61542 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3335, d61542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3335, d61542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3336 q = 1) : d61543 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3336, d61543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3336, d61543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3337 q = 1) : d61544 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3337, d61544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3337, d61544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro1959 (p : Pattern) (selected : d3352 p = 1) : d61555 p = 1 := by
  have h0 (q : Pattern) (selected : d3345 q = 1) : d3345 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3346 q = 1) : d61550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3346, d61550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro19 q selected
    | true =>
      simp only [d3346, d61550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3347 q = 1) : d3347 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3348 q = 1) : d61551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3348, d61551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3348, d61551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3349 q = 1) : d61552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3349, d61552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3349, d61552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3350 q = 1) : d61553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3350, d61553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3350, d61553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3351 q = 1) : d61554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3351, d61554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3351, d61554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3352 q = 1) : d61555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3352, d61555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3352, d61555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro1960 (p : Pattern) (selected : d3358 p = 1) : d61561 p = 1 := by
  have h0 (q : Pattern) (selected : d3328 q = 1) : d3328 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3338 q = 1) : d61545 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3338, d61545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3338, d61545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1958 q selected
  have h3 (q : Pattern) (selected : d3339 q = 1) : d61546 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3339, d61546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3339, d61546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3340 q = 1) : d61547 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3340, d61547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3340, d61547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3341 q = 1) : d61548 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3341, d61548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3341, d61548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3342 q = 1) : d61549 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3342, d61549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3342, d61549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3353 q = 1) : d61556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3353, d61556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3353, d61556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1959 q selected
  have h8 (q : Pattern) (selected : d3354 q = 1) : d61557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3354, d61557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3354, d61557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3355 q = 1) : d61558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3355, d61558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3355, d61558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3356 q = 1) : d61559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3356, d61559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3356, d61559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3357 q = 1) : d61560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3357, d61560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3357, d61560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d3358 q = 1) : d61561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3358, d61561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3358, d61561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro1961 (p : Pattern) (selected : d3368 p = 1) : d61567 p = 1 := by
  have h0 (q : Pattern) (selected : d3361 q = 1) : d3361 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3362 q = 1) : d61562 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3362, d61562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro36 q selected
    | true =>
      simp only [d3362, d61562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3363 q = 1) : d3363 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3364 q = 1) : d61563 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3364, d61563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3364, d61563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3365 q = 1) : d61564 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3365, d61564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3365, d61564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3366 q = 1) : d61565 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3366, d61565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3366, d61565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3367 q = 1) : d61566 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3367, d61566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3367, d61566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3368 q = 1) : d61567 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3368, d61567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3368, d61567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro1962 (p : Pattern) (selected : d3374 p = 1) : d61573 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3369 q = 1) : d61568 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3369, d61568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3369, d61568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1961 q selected
  have h2 (q : Pattern) (selected : d3370 q = 1) : d61569 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3370, d61569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3370, d61569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3371 q = 1) : d61570 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3371, d61570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3371, d61570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3372 q = 1) : d61571 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3372, d61571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3372, d61571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3373 q = 1) : d61572 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3373, d61572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3373, d61572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3374 q = 1) : d61573 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3374, d61573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3374, d61573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1963 (p : Pattern) (selected : d3385 p = 1) : d61580 p = 1 := by
  have h0 (q : Pattern) (selected : d3378 q = 1) : d3378 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3379 q = 1) : d61575 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3379, d61575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro60 q selected
    | true =>
      simp only [d3379, d61575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3380 q = 1) : d3380 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3381 q = 1) : d61576 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3381, d61576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3381, d61576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3382 q = 1) : d61577 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3382, d61577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3382, d61577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3383 q = 1) : d61578 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3383, d61578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3383, d61578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3384 q = 1) : d61579 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3384, d61579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3384, d61579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3385 q = 1) : d61580 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3385, d61580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3385, d61580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro1964 (p : Pattern) (selected : d3391 p = 1) : d61586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3386 q = 1) : d61581 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3386, d61581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3386, d61581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1963 q selected
  have h2 (q : Pattern) (selected : d3387 q = 1) : d61582 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3387, d61582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3387, d61582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3388 q = 1) : d61583 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3388, d61583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3388, d61583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3389 q = 1) : d61584 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3389, d61584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3389, d61584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3390 q = 1) : d61585 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3390, d61585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3390, d61585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3391 q = 1) : d61586 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3391, d61586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3391, d61586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1965 (p : Pattern) (selected : d3403 p = 1) : d61594 p = 1 := by
  have h0 (q : Pattern) (selected : d3396 q = 1) : d3396 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3397 q = 1) : d61589 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3397, d61589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro90 q selected
    | true =>
      simp only [d3397, d61589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3398 q = 1) : d3398 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3399 q = 1) : d61590 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3399, d61590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3399, d61590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3400 q = 1) : d61591 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3400, d61591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3400, d61591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3401 q = 1) : d61592 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3401, d61592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3401, d61592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3402 q = 1) : d61593 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3402, d61593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3402, d61593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3403 q = 1) : d61594 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3403, d61594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3403, d61594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro1966 (p : Pattern) (selected : d3409 p = 1) : d61600 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3404 q = 1) : d61595 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3404, d61595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3404, d61595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1965 q selected
  have h2 (q : Pattern) (selected : d3405 q = 1) : d61596 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3405, d61596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3405, d61596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3406 q = 1) : d61597 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3406, d61597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3406, d61597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3407 q = 1) : d61598 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3407, d61598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3407, d61598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3408 q = 1) : d61599 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3408, d61599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3408, d61599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3409 q = 1) : d61600 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3409, d61600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3409, d61600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1967 (p : Pattern) (selected : d3422 p = 1) : d61609 p = 1 := by
  have h0 (q : Pattern) (selected : d3415 q = 1) : d3415 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3416 q = 1) : d61604 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3416, d61604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro126 q selected
    | true =>
      simp only [d3416, d61604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3417 q = 1) : d3417 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3418 q = 1) : d61605 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3418, d61605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3418, d61605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3419 q = 1) : d61606 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3419, d61606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3419, d61606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3420 q = 1) : d61607 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3420, d61607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3420, d61607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3421 q = 1) : d61608 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3421, d61608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3421, d61608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3422 q = 1) : d61609 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3422, d61609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3422, d61609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro1968 (p : Pattern) (selected : d3428 p = 1) : d61615 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3423 q = 1) : d61610 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3423, d61610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3423, d61610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1967 q selected
  have h2 (q : Pattern) (selected : d3424 q = 1) : d61611 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3424, d61611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3424, d61611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3425 q = 1) : d61612 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3425, d61612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3425, d61612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3426 q = 1) : d61613 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3426, d61613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3426, d61613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3427 q = 1) : d61614 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3427, d61614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3427, d61614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3428 q = 1) : d61615 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3428, d61615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3428, d61615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1969 (p : Pattern) (selected : d3442 p = 1) : d61625 p = 1 := by
  have h0 (q : Pattern) (selected : d3435 q = 1) : d3435 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3436 q = 1) : d61620 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d3436, d61620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro163 q selected
    | true =>
      simp only [d3436, d61620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3437 q = 1) : d3437 q = 1 := by
    exact selected
  have h4 (q : Pattern) (selected : d3438 q = 1) : d61621 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d3438, d61621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3438, d61621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3439 q = 1) : d61622 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d3439, d61622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3439, d61622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d3440 q = 1) : d61623 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d3440, d61623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3440, d61623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3441 q = 1) : d61624 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d3441, d61624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3441, d61624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h8 (q : Pattern) (selected : d3442 q = 1) : d61625 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d3442, d61625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d3442, d61625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h8 p selected
theorem eqIntro1970 (p : Pattern) (selected : d3448 p = 1) : d61631 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3443 q = 1) : d61626 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d3443, d61626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3443, d61626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1969 q selected
  have h2 (q : Pattern) (selected : d3444 q = 1) : d61627 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d3444, d61627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3444, d61627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d3445 q = 1) : d61628 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d3445, d61628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3445, d61628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3446 q = 1) : d61629 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d3446, d61629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3446, d61629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d3447 q = 1) : d61630 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d3447, d61630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3447, d61630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3448 q = 1) : d61631 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d3448, d61631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3448, d61631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1971 (p : Pattern) (selected : d3454 p = 1) : d61637 p = 1 := by
  have h0 (q : Pattern) (selected : d3375 q = 1) : d61574 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3375, d61574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1960 q selected
    | true =>
      simp only [d3375, d61574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1962 q selected
  have h1 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h2 (q : Pattern) (selected : d3392 q = 1) : d61587 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3392, d61587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3392, d61587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1964 q selected
  have h3 (q : Pattern) (selected : d3393 q = 1) : d61588 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3393, d61588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d3393, d61588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d3410 q = 1) : d61601 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3410, d61601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3410, d61601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1966 q selected
  have h5 (q : Pattern) (selected : d3411 q = 1) : d61602 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3411, d61602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3411, d61602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d3412 q = 1) : d61603 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3412, d61603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3412, d61603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d3429 q = 1) : d61616 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3429, d61616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3429, d61616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1968 q selected
  have h8 (q : Pattern) (selected : d3430 q = 1) : d61617 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3430, d61617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3430, d61617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d3431 q = 1) : d61618 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3431, d61618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3431, d61618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d3432 q = 1) : d61619 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3432, d61619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d3432, d61619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d3449 q = 1) : d61632 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d3449, d61632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3449, d61632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1970 q selected
  have h12 (q : Pattern) (selected : d3450 q = 1) : d61633 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d3450, d61633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3450, d61633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d3451 q = 1) : d61634 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d3451, d61634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3451, d61634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d3452 q = 1) : d61635 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d3452, d61635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3452, d61635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d3453 q = 1) : d61636 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d3453, d61636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d3453, d61636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d3454 q = 1) : d61637 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d3454, d61637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d3454, d61637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1972 (p : Pattern) (selected : d3460 p = 1) : d61643 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3455 q = 1) : d61638 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d3455, d61638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1971 q selected
    | true =>
      simp only [d3455, d61638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3456 q = 1) : d61639 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d3456, d61639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3456, d61639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3457 q = 1) : d61640 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d3457, d61640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3457, d61640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3458 q = 1) : d61641 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d3458, d61641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3458, d61641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3459 q = 1) : d61642 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d3459, d61642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3459, d61642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3460 q = 1) : d61643 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d3460, d61643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3460, d61643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1973 (p : Pattern) (selected : d3466 p = 1) : d61649 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3461 q = 1) : d61644 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d3461, d61644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1972 q selected
    | true =>
      simp only [d3461, d61644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3462 q = 1) : d61645 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d3462, d61645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3462, d61645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3463 q = 1) : d61646 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d3463, d61646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3463, d61646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3464 q = 1) : d61647 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d3464, d61647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3464, d61647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3465 q = 1) : d61648 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d3465, d61648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3465, d61648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3466 q = 1) : d61649 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d3466, d61649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3466, d61649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1974 (p : Pattern) (selected : d3472 p = 1) : d61655 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3467 q = 1) : d61650 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d3467, d61650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1973 q selected
    | true =>
      simp only [d3467, d61650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3468 q = 1) : d61651 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d3468, d61651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3468, d61651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3469 q = 1) : d61652 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d3469, d61652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3469, d61652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3470 q = 1) : d61653 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d3470, d61653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3470, d61653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3471 q = 1) : d61654 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d3471, d61654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3471, d61654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3472 q = 1) : d61655 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d3472, d61655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3472, d61655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1975 (p : Pattern) (selected : d3478 p = 1) : d61661 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3473 q = 1) : d61656 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d3473, d61656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1974 q selected
    | true =>
      simp only [d3473, d61656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3474 q = 1) : d61657 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d3474, d61657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3474, d61657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3475 q = 1) : d61658 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d3475, d61658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3475, d61658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3476 q = 1) : d61659 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d3476, d61659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3476, d61659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3477 q = 1) : d61660 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d3477, d61660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3477, d61660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3478 q = 1) : d61661 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d3478, d61661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3478, d61661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1976 (p : Pattern) (selected : d3484 p = 1) : d61667 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3479 q = 1) : d61662 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d3479, d61662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1975 q selected
    | true =>
      simp only [d3479, d61662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3480 q = 1) : d61663 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d3480, d61663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3480, d61663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3481 q = 1) : d61664 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d3481, d61664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3481, d61664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3482 q = 1) : d61665 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d3482, d61665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3482, d61665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3483 q = 1) : d61666 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d3483, d61666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3483, d61666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3484 q = 1) : d61667 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d3484, d61667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3484, d61667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1977 (p : Pattern) (selected : d3490 p = 1) : d61673 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3485 q = 1) : d61668 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d3485, d61668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1976 q selected
    | true =>
      simp only [d3485, d61668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3486 q = 1) : d61669 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d3486, d61669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3486, d61669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3487 q = 1) : d61670 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d3487, d61670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3487, d61670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3488 q = 1) : d61671 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d3488, d61671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3488, d61671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3489 q = 1) : d61672 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d3489, d61672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3489, d61672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3490 q = 1) : d61673 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d3490, d61673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3490, d61673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1978 (p : Pattern) (selected : d3496 p = 1) : d61679 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 1) : d0 q = 1 := by
    exact selected
  have h1 (q : Pattern) (selected : d3491 q = 1) : d61674 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d3491, d61674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1977 q selected
    | true =>
      simp only [d3491, d61674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d3492 q = 1) : d61675 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d3492, d61675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d3492, d61675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d3493 q = 1) : d61676 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d3493, d61676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d3493, d61676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d3494 q = 1) : d61677 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d3494, d61677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d3494, d61677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d3495 q = 1) : d61678 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d3495, d61678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d3495, d61678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d3496 q = 1) : d61679 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d3496, d61679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d3496, d61679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1979 (p : Pattern) (selected : d2672 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d56 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro649 q selected
    | true =>
      simp only [d56, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro651 q selected
  have h2 (q : Pattern) (selected : d57 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d57, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d58 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d58, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d59 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d59, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d61 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d61, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro652 q selected
  have h6 (q : Pattern) (selected : d62 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d62, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d63 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d63, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d64 q = 2) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d64, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d65 q = 2) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d65, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2672 q = 2) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro1980 (p : Pattern) (selected : d2677 p = 2) : d54404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d105 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d105, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
  have h2 (q : Pattern) (selected : d106 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d106, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d112 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro658 q selected
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h4 (q : Pattern) (selected : d113 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d114 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d212 q = 2) : d112 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d212, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro672 q selected
    | true =>
      simp only [d212, d112, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro677 q selected
  have h7 (q : Pattern) (selected : d214 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro678 q selected
    | true =>
      simp only [d214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d215 q = 2) : d113 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d215, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d215, d113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d216 q = 2) : d53637 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d216, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d216, d53637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d217 q = 2) : d53638 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d217, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d217, d53638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d221 q = 2) : d407 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d221, d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d221, d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro679 q selected
  have h12 (q : Pattern) (selected : d222 q = 2) : d53639 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d222, d53639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d222, d53639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d223 q = 2) : d53640 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d223, d53640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d223, d53640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d224 q = 2) : d53641 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d224, d53641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d224, d53641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d225 q = 2) : d53642 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d225, d53642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d225, d53642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d2677 q = 2) : d54404 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2677, d54404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d2677, d54404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro1981 (p : Pattern) (selected : d2683 p = 2) : d54410 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d285 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro688 q selected
  have h2 (q : Pattern) (selected : d286 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d292 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro688 q selected
    | true =>
      simp only [d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro689 q selected
  have h4 (q : Pattern) (selected : d293 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d294 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d396 q = 2) : d292 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d396, d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro702 q selected
    | true =>
      simp only [d396, d292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro707 q selected
  have h7 (q : Pattern) (selected : d398 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro708 q selected
    | true =>
      simp only [d398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro659 q selected
  have h8 (q : Pattern) (selected : d399 q = 2) : d293 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d399, d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d399, d293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d400 q = 2) : d53653 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d400, d53653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d400, d53653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d401 q = 2) : d53654 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d401, d53654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d401, d53654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d405 q = 2) : d53656 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d405, d53656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d405, d53656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro709 q selected
  have h12 (q : Pattern) (selected : d407 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro710 q selected
  have h13 (q : Pattern) (selected : d408 q = 2) : d53657 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d408, d53657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d408, d53657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d409 q = 2) : d53658 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d409, d53658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d409, d53658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d410 q = 2) : d53659 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d410, d53659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d410, d53659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d411 q = 2) : d53660 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d411, d53660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d411, d53660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d2683 q = 2) : d54410 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2683, d54410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d2683, d54410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h17 p selected
theorem eqIntro1982 (p : Pattern) (selected : d2689 p = 2) : d54416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2673 q = 2) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1979 q selected
  have h2 (q : Pattern) (selected : d2674 q = 2) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2675 q = 2) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2676 q = 2) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2678 q = 2) : d54405 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2678, d54405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2678, d54405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1980 q selected
  have h6 (q : Pattern) (selected : d2679 q = 2) : d54406 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2679, d54406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2679, d54406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2680 q = 2) : d54407 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2680, d54407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2680, d54407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d2681 q = 2) : d54408 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2681, d54408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2681, d54408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2682 q = 2) : d54409 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2682, d54409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2682, d54409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2684 q = 2) : d54411 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2684, d54411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2684, d54411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1981 q selected
  have h11 (q : Pattern) (selected : d2685 q = 2) : d54412 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2685, d54412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2685, d54412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d2686 q = 2) : d54413 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2686, d54413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2686, d54413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2687 q = 2) : d54414 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2687, d54414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2687, d54414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2688 q = 2) : d54415 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2688, d54415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2688, d54415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2689 q = 2) : d54416 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2689, d54416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d2689, d54416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro1983 (p : Pattern) (selected : d2690 p = 2) : d54417 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d498 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro725 q selected
  have h2 (q : Pattern) (selected : d499 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d508 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro725 q selected
    | true =>
      simp only [d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro728 q selected
  have h4 (q : Pattern) (selected : d509 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d510 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d632 q = 2) : d508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d632, d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro746 q selected
    | true =>
      simp only [d632, d508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro754 q selected
  have h7 (q : Pattern) (selected : d645 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro755 q selected
    | true =>
      simp only [d645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro756 q selected
  have h8 (q : Pattern) (selected : d646 q = 2) : d509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d646, d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d646, d509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d647 q = 2) : d53678 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d647, d53678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d647, d53678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d648 q = 2) : d53679 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d648, d53679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d648, d53679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d652 q = 2) : d53681 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d652, d53681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d652, d53681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro757 q selected
  have h12 (q : Pattern) (selected : d654 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro758 q selected
  have h13 (q : Pattern) (selected : d655 q = 2) : d53682 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d655, d53682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d655, d53682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d656 q = 2) : d53683 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d656, d53683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d656, d53683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d657 q = 2) : d53684 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d657, d53684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d657, d53684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d658 q = 2) : d53685 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d658, d53685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d658, d53685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d2690 q = 2) : d54417 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2690, d54417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d2690, d54417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h17 p selected
theorem eqIntro1984 (p : Pattern) (selected : d2696 p = 2) : d54423 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2691 q = 2) : d54418 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2691, d54418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2691, d54418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1983 q selected
  have h2 (q : Pattern) (selected : d2692 q = 2) : d54419 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2692, d54419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2692, d54419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2693 q = 2) : d54420 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2693, d54420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2693, d54420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2694 q = 2) : d54421 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2694, d54421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2694, d54421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2695 q = 2) : d54422 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2695, d54422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2695, d54422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2696 q = 2) : d54423 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2696, d54423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2696, d54423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1985 (p : Pattern) (selected : d2698 p = 2) : d54425 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d790 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro783 q selected
  have h2 (q : Pattern) (selected : d791 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d800 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro783 q selected
    | true =>
      simp only [d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro786 q selected
  have h4 (q : Pattern) (selected : d801 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d802 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d938 q = 2) : d800 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d938, d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro808 q selected
    | true =>
      simp only [d938, d800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro816 q selected
  have h7 (q : Pattern) (selected : d951 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro817 q selected
    | true =>
      simp only [d951, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro818 q selected
  have h8 (q : Pattern) (selected : d952 q = 2) : d801 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d952, d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d952, d801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d953 q = 2) : d53705 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d953, d53705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d953, d53705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d954 q = 2) : d53706 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d954, d53706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d954, d53706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d958 q = 2) : d53708 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d958, d53708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d958, d53708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro819 q selected
  have h12 (q : Pattern) (selected : d960 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro820 q selected
  have h13 (q : Pattern) (selected : d961 q = 2) : d53709 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d961, d53709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d961, d53709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d962 q = 2) : d53710 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d962, d53710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d962, d53710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d963 q = 2) : d53711 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d963, d53711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d963, d53711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d964 q = 2) : d53712 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d964, d53712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d964, d53712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d2698 q = 2) : d54425 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2698, d54425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d2698, d54425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h17 p selected
theorem eqIntro1986 (p : Pattern) (selected : d2704 p = 2) : d54431 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2699 q = 2) : d54426 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2699, d54426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2699, d54426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1985 q selected
  have h2 (q : Pattern) (selected : d2700 q = 2) : d54427 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2700, d54427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2700, d54427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2701 q = 2) : d54428 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2701, d54428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2701, d54428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2702 q = 2) : d54429 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2702, d54429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2702, d54429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2703 q = 2) : d54430 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2703, d54430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2703, d54430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2704 q = 2) : d54431 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2704, d54431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2704, d54431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1987 (p : Pattern) (selected : d2707 p = 2) : d54434 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1169 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1169, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro855 q selected
  have h2 (q : Pattern) (selected : d1170 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1170, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1179 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro855 q selected
    | true =>
      simp only [d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro858 q selected
  have h4 (q : Pattern) (selected : d1180 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1181 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1181, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1349 q = 2) : d1179 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1349, d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro884 q selected
    | true =>
      simp only [d1349, d1179, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro892 q selected
  have h7 (q : Pattern) (selected : d1362 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro893 q selected
    | true =>
      simp only [d1362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro894 q selected
  have h8 (q : Pattern) (selected : d1363 q = 2) : d1180 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1363, d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1363, d1180, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1364 q = 2) : d53733 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1364, d53733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1364, d53733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1365 q = 2) : d53734 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1365, d53734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1365, d53734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1369 q = 2) : d53736 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1369, d53736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1369, d53736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro895 q selected
  have h12 (q : Pattern) (selected : d1371 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro896 q selected
  have h13 (q : Pattern) (selected : d1372 q = 2) : d53737 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1372, d53737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1372, d53737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1373 q = 2) : d53738 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1373, d53738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1373, d53738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d1374 q = 2) : d53739 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1374, d53739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d1374, d53739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d1375 q = 2) : d53740 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d1375, d53740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1375, d53740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d2707 q = 2) : d54434 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2707, d54434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d2707, d54434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h17 p selected
theorem eqIntro1988 (p : Pattern) (selected : d2713 p = 2) : d54440 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2708 q = 2) : d54435 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2708, d54435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2708, d54435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1987 q selected
  have h2 (q : Pattern) (selected : d2709 q = 2) : d54436 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2709, d54436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2709, d54436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2710 q = 2) : d54437 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2710, d54437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2710, d54437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2711 q = 2) : d54438 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2711, d54438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2711, d54438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2712 q = 2) : d54439 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2712, d54439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2712, d54439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2713 q = 2) : d54440 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2713, d54440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2713, d54440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1989 (p : Pattern) (selected : d2717 p = 2) : d54444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1630 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro937 q selected
  have h2 (q : Pattern) (selected : d1631 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d1631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d1640 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro937 q selected
    | true =>
      simp only [d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro940 q selected
  have h4 (q : Pattern) (selected : d1641 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d1642 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d1642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d1826 q = 2) : d1640 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1826, d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro970 q selected
    | true =>
      simp only [d1826, d1640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro978 q selected
  have h7 (q : Pattern) (selected : d1839 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro979 q selected
    | true =>
      simp only [d1839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro980 q selected
  have h8 (q : Pattern) (selected : d1840 q = 2) : d1641 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1840, d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d1840, d1641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d1841 q = 2) : d53762 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1841, d53762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d1841, d53762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d1842 q = 2) : d53763 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1842, d53763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d1842, d53763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d1846 q = 2) : d53765 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1846, d53765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1846, d53765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro981 q selected
  have h12 (q : Pattern) (selected : d1848 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d1848, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro982 q selected
  have h13 (q : Pattern) (selected : d1849 q = 2) : d53766 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d1849, d53766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d1849, d53766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d1850 q = 2) : d53767 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d1850, d53767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d1850, d53767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d1851 q = 2) : d53768 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d1851, d53768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d1851, d53768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d1852 q = 2) : d53769 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d1852, d53769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d1852, d53769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d2717 q = 2) : d54444 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2717, d54444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d2717, d54444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h17 p selected
theorem eqIntro1990 (p : Pattern) (selected : d2723 p = 2) : d54450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2718 q = 2) : d54445 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2718, d54445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2718, d54445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1989 q selected
  have h2 (q : Pattern) (selected : d2719 q = 2) : d54446 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2719, d54446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2719, d54446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2720 q = 2) : d54447 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2720, d54447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2720, d54447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2721 q = 2) : d54448 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2721, d54448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2721, d54448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2722 q = 2) : d54449 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2722, d54449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2722, d54449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2723 q = 2) : d54450 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2723, d54450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2723, d54450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1991 (p : Pattern) (selected : d2728 p = 2) : d54455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2113 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2113, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1026 q selected
  have h2 (q : Pattern) (selected : d2114 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2114, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2123 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1026 q selected
    | true =>
      simp only [d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1029 q selected
  have h4 (q : Pattern) (selected : d2124 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2125 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2125, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2304 q = 2) : d2123 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2304, d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1060 q selected
    | true =>
      simp only [d2304, d2123, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1068 q selected
  have h7 (q : Pattern) (selected : d2317 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1069 q selected
    | true =>
      simp only [d2317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1070 q selected
  have h8 (q : Pattern) (selected : d2318 q = 2) : d2124 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2318, d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2318, d2124, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2319 q = 2) : d53792 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2319, d53792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d2319, d53792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d2320 q = 2) : d53793 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2320, d53793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2320, d53793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2324 q = 2) : d53795 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2324, d53795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2324, d53795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1071 q selected
  have h12 (q : Pattern) (selected : d2326 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1072 q selected
  have h13 (q : Pattern) (selected : d2327 q = 2) : d53796 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d2327, d53796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d2327, d53796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2328 q = 2) : d53797 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d2328, d53797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d2328, d53797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d2329 q = 2) : d53798 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d2329, d53798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d2329, d53798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d2330 q = 2) : d53799 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d2330, d53799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2330, d53799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d2728 q = 2) : d54455 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d2728, d54455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d2728, d54455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h17 p selected
theorem eqIntro1992 (p : Pattern) (selected : d2734 p = 2) : d54461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2729 q = 2) : d54456 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d2729, d54456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2729, d54456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1991 q selected
  have h2 (q : Pattern) (selected : d2730 q = 2) : d54457 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d2730, d54457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2730, d54457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d2731 q = 2) : d54458 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d2731, d54458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2731, d54458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2732 q = 2) : d54459 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d2732, d54459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2732, d54459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d2733 q = 2) : d54460 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d2733, d54460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2733, d54460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2734 q = 2) : d54461 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d2734, d54461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2734, d54461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro1993 (p : Pattern) (selected : d2740 p = 2) : d54467 p = 1 := by
  have h0 (q : Pattern) (selected : d2697 q = 2) : d54424 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2697, d54424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1982 q selected
    | true =>
      simp only [d2697, d54424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1984 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d2705 q = 2) : d54432 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2705, d54432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2705, d54432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1986 q selected
  have h3 (q : Pattern) (selected : d2706 q = 2) : d54433 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2706, d54433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d2706, d54433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d2714 q = 2) : d54441 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2714, d54441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2714, d54441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1988 q selected
  have h5 (q : Pattern) (selected : d2715 q = 2) : d54442 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2715, d54442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2715, d54442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d2716 q = 2) : d54443 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2716, d54443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2716, d54443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d2724 q = 2) : d54451 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2724, d54451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2724, d54451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1990 q selected
  have h8 (q : Pattern) (selected : d2725 q = 2) : d54452 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2725, d54452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2725, d54452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d2726 q = 2) : d54453 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2726, d54453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2726, d54453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d2727 q = 2) : d54454 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2727, d54454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d2727, d54454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d2735 q = 2) : d54462 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d2735, d54462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2735, d54462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1992 q selected
  have h12 (q : Pattern) (selected : d2736 q = 2) : d54463 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d2736, d54463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2736, d54463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d2737 q = 2) : d54464 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d2737, d54464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2737, d54464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d2738 q = 2) : d54465 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d2738, d54465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2738, d54465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d2739 q = 2) : d54466 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d2739, d54466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d2739, d54466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d2740 q = 2) : d54467 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d2740, d54467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d2740, d54467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro1994 (p : Pattern) (selected : d2746 p = 2) : d54473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2741 q = 2) : d54468 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d2741, d54468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1993 q selected
    | true =>
      simp only [d2741, d54468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2742 q = 2) : d54469 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d2742, d54469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2742, d54469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2743 q = 2) : d54470 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d2743, d54470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2743, d54470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2744 q = 2) : d54471 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d2744, d54471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2744, d54471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2745 q = 2) : d54472 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d2745, d54472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2745, d54472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2746 q = 2) : d54473 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d2746, d54473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2746, d54473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1995 (p : Pattern) (selected : d2752 p = 2) : d54479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2747 q = 2) : d54474 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d2747, d54474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1994 q selected
    | true =>
      simp only [d2747, d54474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2748 q = 2) : d54475 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d2748, d54475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2748, d54475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2749 q = 2) : d54476 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d2749, d54476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2749, d54476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2750 q = 2) : d54477 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d2750, d54477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2750, d54477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2751 q = 2) : d54478 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d2751, d54478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2751, d54478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2752 q = 2) : d54479 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d2752, d54479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2752, d54479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1996 (p : Pattern) (selected : d2758 p = 2) : d54485 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2753 q = 2) : d54480 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d2753, d54480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1995 q selected
    | true =>
      simp only [d2753, d54480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2754 q = 2) : d54481 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d2754, d54481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2754, d54481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2755 q = 2) : d54482 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d2755, d54482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2755, d54482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2756 q = 2) : d54483 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d2756, d54483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2756, d54483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2757 q = 2) : d54484 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d2757, d54484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2757, d54484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2758 q = 2) : d54485 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d2758, d54485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2758, d54485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1997 (p : Pattern) (selected : d2764 p = 2) : d54491 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2759 q = 2) : d54486 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d2759, d54486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1996 q selected
    | true =>
      simp only [d2759, d54486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2760 q = 2) : d54487 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d2760, d54487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2760, d54487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2761 q = 2) : d54488 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d2761, d54488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2761, d54488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2762 q = 2) : d54489 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d2762, d54489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2762, d54489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2763 q = 2) : d54490 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d2763, d54490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2763, d54490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2764 q = 2) : d54491 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d2764, d54491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2764, d54491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1998 (p : Pattern) (selected : d2770 p = 2) : d54497 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2765 q = 2) : d54492 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d2765, d54492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1997 q selected
    | true =>
      simp only [d2765, d54492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2766 q = 2) : d54493 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d2766, d54493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2766, d54493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2767 q = 2) : d54494 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d2767, d54494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2767, d54494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2768 q = 2) : d54495 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d2768, d54495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2768, d54495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2769 q = 2) : d54496 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d2769, d54496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2769, d54496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2770 q = 2) : d54497 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d2770, d54497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2770, d54497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro1999 (p : Pattern) (selected : d2776 p = 2) : d54503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2771 q = 2) : d54498 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d2771, d54498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro1998 q selected
    | true =>
      simp only [d2771, d54498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d2772 q = 2) : d54499 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d2772, d54499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d2772, d54499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d2773 q = 2) : d54500 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d2773, d54500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d2773, d54500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d2774 q = 2) : d54501 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d2774, d54501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d2774, d54501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d2775 q = 2) : d54502 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d2775, d54502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d2775, d54502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d2776 q = 2) : d54503 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d2776, d54503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d2776, d54503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
end NetHack.Soko22Hazard87
