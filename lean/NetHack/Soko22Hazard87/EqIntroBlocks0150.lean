import NetHack.Soko22Hazard87.EqIntroBlocks0149
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem eqIntro37500 (p : Pattern) (selected : d44371 p = 2) : d44318 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44361 q = 2) : d44300 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44361, d44300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37497 q selected
    | true =>
      simp only [d44361, d44300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37498 q selected
  have h2 (q : Pattern) (selected : d44362 q = 2) : d44301 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44362, d44301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44362, d44301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44363 q = 2) : d44302 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44363, d44302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44363, d44302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44365 q = 2) : d44308 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44365, d44308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44365, d44308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44370 q = 2) : d44317 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44370, d44317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44370, d44317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44371 q = 2) : d44318 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44371, d44318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44371, d44318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37501 (p : Pattern) (selected : d44377 p = 2) : d44324 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44368 q = 2) : d44311 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44368, d44311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37499 q selected
    | true =>
      simp only [d44368, d44311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44369 q = 2) : d44312 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44369, d44312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44369, d44312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44372 q = 2) : d44319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44372, d44319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37500 q selected
    | true =>
      simp only [d44372, d44319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44373 q = 2) : d44320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44373, d44320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44373, d44320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44374 q = 2) : d44321 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44374, d44321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44374, d44321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44375 q = 2) : d44322 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44375, d44322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44375, d44322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44376 q = 2) : d44323 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44376, d44323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44376, d44323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44377 q = 2) : d44324 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44377, d44324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44377, d44324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37502 (p : Pattern) (selected : d44381 p = 2) : d44418 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44372 q = 2) : d44319 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44372, d44319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37500 q selected
    | true =>
      simp only [d44372, d44319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44373 q = 2) : d44320 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44373, d44320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44373, d44320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44378 q = 2) : d44415 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44378, d44415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44378, d44415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44379 q = 2) : d44416 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44379, d44416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44379, d44416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44380 q = 2) : d44417 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44380, d44417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44380, d44417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44381 q = 2) : d44418 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44381, d44418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44381, d44418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37503 (p : Pattern) (selected : d44389 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44285 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37425 q selected
  have h2 (q : Pattern) (selected : d43916 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37425 q selected
    | true =>
      simp only [d43916, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44286 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d43917 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d43917, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44287 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44288 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44289 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37426 q selected
  have h8 (q : Pattern) (selected : d43921 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d43921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37426 q selected
    | true =>
      simp only [d43921, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44290 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d43922 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d43922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d43922, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44291 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d44292 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44293 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44384 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37466 q selected
  have h15 (q : Pattern) (selected : d44155 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37466 q selected
    | true =>
      simp only [d44155, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d44385 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d44385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d44156 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d44156, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d44386 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d44386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d44387 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d44387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d44388 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d44388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d44389 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro37504 (p : Pattern) (selected : d44395 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44390 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37468 q selected
  have h2 (q : Pattern) (selected : d44162 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37468 q selected
    | true =>
      simp only [d44162, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44391 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44163 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44163, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44392 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44393 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44394 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44395 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37505 (p : Pattern) (selected : d44401 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44295 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37487 q selected
    | true =>
      simp only [d44295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37489 q selected
  have h2 (q : Pattern) (selected : d44296 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44297 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44300 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37489 q selected
    | true =>
      simp only [d44300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37490 q selected
  have h5 (q : Pattern) (selected : d44301 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44302 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44303 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44396 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37503 q selected
    | true =>
      simp only [d44396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37504 q selected
  have h9 (q : Pattern) (selected : d44397 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44398 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44399 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44400 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44401 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro37506 (p : Pattern) (selected : d44407 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44402 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37505 q selected
    | true =>
      simp only [d44402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44403 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44404 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44405 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44406 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44407 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37507 (p : Pattern) (selected : d44413 p = 2) : d357538 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44325 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37493 q selected
    | true =>
      simp only [d44325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37495 q selected
  have h2 (q : Pattern) (selected : d44382 q = 2) : d357533 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44382, d357533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37501 q selected
    | true =>
      simp only [d44382, d357533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37502 q selected
  have h3 (q : Pattern) (selected : d44383 q = 2) : d357534 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44383, d357534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44383, d357534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44408 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37506 q selected
    | true =>
      simp only [d44408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44409 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44410 q = 2) : d357535 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44410, d357535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44410, d357535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44411 q = 2) : d357536 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44411, d357536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44411, d357536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44412 q = 2) : d357537 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44412, d357537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44412, d357537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44413 q = 2) : d357538 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44413, d357538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44413, d357538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37508 (p : Pattern) (selected : d44418 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44319 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37494 q selected
    | true =>
      simp only [d44319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44320 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44415 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44416 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44417 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44418 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37509 (p : Pattern) (selected : d44424 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44419 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37508 q selected
    | true =>
      simp only [d44419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44420 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44421 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44422 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44423 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44424 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37510 (p : Pattern) (selected : d44430 p = 2) : d357544 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d43960 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d43960, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37433 q selected
  have h2 (q : Pattern) (selected : d43961 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d43961, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d43970 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d43970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37433 q selected
    | true =>
      simp only [d43970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37436 q selected
  have h4 (q : Pattern) (selected : d43971 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d43971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d43971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d43972 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d43972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d43972, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44210 q = 2) : d43970 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44210, d43970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37472 q selected
    | true =>
      simp only [d44210, d43970, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37481 q selected
  have h7 (q : Pattern) (selected : d44223 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37482 q selected
    | true =>
      simp only [d44223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37483 q selected
  have h8 (q : Pattern) (selected : d44224 q = 2) : d43971 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44224, d43971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44224, d43971, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44225 q = 2) : d357525 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44225, d357525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44225, d357525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44226 q = 2) : d357526 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44226, d357526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44226, d357526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44230 q = 2) : d357528 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44230, d357528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44230, d357528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37484 q selected
  have h12 (q : Pattern) (selected : d44232 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37485 q selected
  have h13 (q : Pattern) (selected : d44233 q = 2) : d357529 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44233, d357529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44233, d357529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44234 q = 2) : d357530 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44234, d357530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44234, d357530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44235 q = 2) : d357531 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44235, d357531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d44235, d357531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d44236 q = 2) : d357532 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d44236, d357532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44236, d357532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d44414 q = 2) : d357539 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44414, d357539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44414, d357539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37507 q selected
  have h18 (q : Pattern) (selected : d44425 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37509 q selected
  have h19 (q : Pattern) (selected : d44426 q = 2) : d357540 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44426, d357540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d44426, d357540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d44427 q = 2) : d357541 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44427, d357541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d44427, d357541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d44428 q = 2) : d357542 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44428, d357542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d44428, d357542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d44429 q = 2) : d357543 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d44429, d357543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d44429, d357543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d44430 q = 2) : d357544 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d44430, d357544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d44430, d357544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro37511 (p : Pattern) (selected : d44436 p = 2) : d357550 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44431 q = 2) : d357545 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d44431, d357545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44431, d357545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37510 q selected
  have h2 (q : Pattern) (selected : d44432 q = 2) : d357546 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d44432, d357546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44432, d357546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44433 q = 2) : d357547 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d44433, d357547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44433, d357547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44434 q = 2) : d357548 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d44434, d357548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44434, d357548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44435 q = 2) : d357549 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d44435, d357549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44435, d357549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44436 q = 2) : d357550 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d44436, d357550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44436, d357550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37512 (p : Pattern) (selected : d44444 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d35372 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30479 q selected
  have h2 (q : Pattern) (selected : d10055 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10598 q selected
  have h3 (q : Pattern) (selected : d35373 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44441 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44442 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44443 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44444 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro37513 (p : Pattern) (selected : d44450 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d1 q = 2) : d0 q = 1 := by
    change (1 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d127 q = 2) : d0 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d308 q = 2) : d0 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1519 q = 2) : d0 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d34366 q = 2) : d0 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d34366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d34367 q = 2) : d0 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d34367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d34367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44450 q = 2) : d0 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro37514 (p : Pattern) (selected : d44459 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d35372 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30479 q selected
  have h2 (q : Pattern) (selected : d10055 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10598 q selected
  have h3 (q : Pattern) (selected : d35373 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44441 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44442 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44443 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44451 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37513 q selected
  have h8 (q : Pattern) (selected : d5128 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro926 q selected
  have h9 (q : Pattern) (selected : d44452 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44453 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44454 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37513 q selected
    | true =>
      simp only [d44454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d1564 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro926 q selected
    | true =>
      simp only [d1564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44455 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44456 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44457 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d44458 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d44458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d44459 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro37515 (p : Pattern) (selected : d44465 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44445 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44446 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44447 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44448 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44449 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44460 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44461 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44462 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44463 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44464 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44465 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37516 (p : Pattern) (selected : d44467 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44445 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44446 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44447 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44448 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44460 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44461 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44462 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44463 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44464 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44466 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44467 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37517 (p : Pattern) (selected : d44471 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44451 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37513 q selected
  have h2 (q : Pattern) (selected : d5128 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d5128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro926 q selected
  have h3 (q : Pattern) (selected : d44452 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44453 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44454 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37513 q selected
    | true =>
      simp only [d44454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1564 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro926 q selected
    | true =>
      simp only [d1564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44455 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44456 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44457 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44458 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44471 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro37518 (p : Pattern) (selected : d44477 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44460 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44461 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44462 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44463 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44466 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44472 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37517 q selected
    | true =>
      simp only [d44472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44473 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44474 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44475 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44476 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44477 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37519 (p : Pattern) (selected : d44484 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44468 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37515 q selected
    | true =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37516 q selected
  have h2 (q : Pattern) (selected : d44469 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44470 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44478 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37516 q selected
    | true =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37518 q selected
  have h5 (q : Pattern) (selected : d44479 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44480 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44481 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44482 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44483 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44484 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37520 (p : Pattern) (selected : d44488 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44478 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37516 q selected
    | true =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37518 q selected
  have h2 (q : Pattern) (selected : d44479 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44480 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44482 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44487 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44488 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37521 (p : Pattern) (selected : d44494 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44485 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37519 q selected
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44486 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44491 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44492 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44493 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44494 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37522 (p : Pattern) (selected : d44498 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44495 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44496 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44497 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44498 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37523 (p : Pattern) (selected : d44504 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44499 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37521 q selected
    | true =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37522 q selected
  have h2 (q : Pattern) (selected : d44500 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44501 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44502 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44503 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44504 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37524 (p : Pattern) (selected : d44507 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44485 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37519 q selected
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44486 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44491 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44492 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44493 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44507 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37525 (p : Pattern) (selected : d44508 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44495 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44496 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44497 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44508 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37526 (p : Pattern) (selected : d44514 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44499 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37521 q selected
    | true =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37522 q selected
  have h2 (q : Pattern) (selected : d44500 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44501 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44502 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44503 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44509 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37524 q selected
    | true =>
      simp only [d44509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37525 q selected
  have h7 (q : Pattern) (selected : d44510 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44511 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44512 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44513 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44514 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37527 (p : Pattern) (selected : d44519 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44485 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37519 q selected
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44486 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44491 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44492 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44518 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44519 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37528 (p : Pattern) (selected : d44521 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44495 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44496 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44520 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44521 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37529 (p : Pattern) (selected : d44528 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44485 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37519 q selected
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44486 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44491 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44526 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44527 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44528 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37530 (p : Pattern) (selected : d44531 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44495 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44529 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44530 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44531 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37531 (p : Pattern) (selected : d44535 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44445 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44446 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44447 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44448 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44449 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44535 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37532 (p : Pattern) (selected : d44541 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44536 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37531 q selected
    | true =>
      simp only [d44536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37515 q selected
  have h2 (q : Pattern) (selected : d44537 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44538 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44468 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37515 q selected
    | true =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37516 q selected
  have h5 (q : Pattern) (selected : d44469 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44470 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44539 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44478 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37516 q selected
    | true =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37518 q selected
  have h9 (q : Pattern) (selected : d44479 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44480 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44481 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d44540 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44541 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro37533 (p : Pattern) (selected : d44547 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44542 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37532 q selected
    | true =>
      simp only [d44542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44543 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44485 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37519 q selected
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44486 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44544 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44545 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44546 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44547 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37534 (p : Pattern) (selected : d44552 p = 2) : d44444 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d35539 q = 2) : d35372 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35539, d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35539, d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30506 q selected
  have h2 (q : Pattern) (selected : d10181 q = 2) : d10055 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10616 q selected
  have h3 (q : Pattern) (selected : d35540 q = 2) : d35373 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35540, d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d35540, d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44549 q = 2) : d44441 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44549, d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44549, d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44550 q = 2) : d44442 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44550, d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44550, d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44551 q = 2) : d44443 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44551, d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44551, d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44552 q = 2) : d44444 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44552, d44444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44552, d44444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  exact h7 p selected
theorem eqIntro37535 (p : Pattern) (selected : d44558 p = 2) : d44450 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d2 q = 2) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d338 q = 2) : d127 q = 1 := by
    cases bit : q 248 with
    | false =>
      simp only [d338, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d338, d127, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d563 q = 2) : d308 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d563, d308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d563, d308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d1687 q = 2) : d1519 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d1687, d1519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d1687, d1519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d34990 q = 2) : d34366 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d34990, d34366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d34990, d34366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d34991 q = 2) : d34367 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d34991, d34367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d34991, d34367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44558 q = 2) : d44450 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d44558, d44450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44558, d44450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro37536 (p : Pattern) (selected : d44567 p = 2) : d44459 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d35539 q = 2) : d35372 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35539, d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35539, d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30506 q selected
  have h2 (q : Pattern) (selected : d10181 q = 2) : d10055 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10181, d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10616 q selected
  have h3 (q : Pattern) (selected : d35540 q = 2) : d35373 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35540, d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d35540, d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44549 q = 2) : d44441 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44549, d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44549, d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44550 q = 2) : d44442 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44550, d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44550, d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44551 q = 2) : d44443 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44551, d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44551, d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44559 q = 2) : d44451 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44559, d44451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44559, d44451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37535 q selected
  have h8 (q : Pattern) (selected : d10209 q = 2) : d5128 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10209, d5128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10209, d5128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro959 q selected
  have h9 (q : Pattern) (selected : d44560 q = 2) : d44452 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44560, d44452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44560, d44452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44561 q = 2) : d44453 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44561, d44453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44561, d44453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44562 q = 2) : d44454 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44562, d44454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37535 q selected
    | true =>
      simp only [d44562, d44454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d1735 q = 2) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d1564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro959 q selected
    | true =>
      simp only [d1735, d1564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44563 q = 2) : d44455 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44563, d44455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44563, d44455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44564 q = 2) : d44456 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44564, d44456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44564, d44456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44565 q = 2) : d44457 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44565, d44457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44565, d44457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d44566 q = 2) : d44458 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44566, d44458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d44566, d44458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d44567 q = 2) : d44459 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44567, d44459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44567, d44459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  exact h17 p selected
theorem eqIntro37537 (p : Pattern) (selected : d44573 p = 2) : d44465 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44553 q = 2) : d44445 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44553, d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37534 q selected
    | true =>
      simp only [d44553, d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44554 q = 2) : d44446 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44554, d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44554, d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44555 q = 2) : d44447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44555, d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44555, d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44556 q = 2) : d44448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44556, d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44556, d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44557 q = 2) : d44449 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44557, d44449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44557, d44449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44568 q = 2) : d44460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
    | true =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44569 q = 2) : d44461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44570 q = 2) : d44462 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44570, d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44570, d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44571 q = 2) : d44463 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44571, d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44571, d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44572 q = 2) : d44464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44572, d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44572, d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44573 q = 2) : d44465 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44573, d44465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44573, d44465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37538 (p : Pattern) (selected : d44575 p = 2) : d44467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44553 q = 2) : d44445 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44553, d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37534 q selected
    | true =>
      simp only [d44553, d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44554 q = 2) : d44446 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44554, d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44554, d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44555 q = 2) : d44447 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44555, d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44555, d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44556 q = 2) : d44448 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44556, d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44556, d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44568 q = 2) : d44460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
    | true =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44569 q = 2) : d44461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44570 q = 2) : d44462 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44570, d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44570, d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44571 q = 2) : d44463 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44571, d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44571, d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44572 q = 2) : d44464 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44572, d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44572, d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44574 q = 2) : d44466 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44574, d44466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44574, d44466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44575 q = 2) : d44467 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44575, d44467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44575, d44467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37539 (p : Pattern) (selected : d44579 p = 2) : d44471 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44559 q = 2) : d44451 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44559, d44451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44559, d44451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37535 q selected
  have h2 (q : Pattern) (selected : d10209 q = 2) : d5128 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10209, d5128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10209, d5128, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro959 q selected
  have h3 (q : Pattern) (selected : d44560 q = 2) : d44452 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44560, d44452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44560, d44452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44561 q = 2) : d44453 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44561, d44453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44561, d44453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44562 q = 2) : d44454 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d44562, d44454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37535 q selected
    | true =>
      simp only [d44562, d44454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d1735 q = 2) : d1564 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1735, d1564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro959 q selected
    | true =>
      simp only [d1735, d1564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44563 q = 2) : d44455 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d44563, d44455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44563, d44455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44564 q = 2) : d44456 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44564, d44456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44564, d44456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44565 q = 2) : d44457 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44565, d44457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44565, d44457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44566 q = 2) : d44458 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44566, d44458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44566, d44458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44579 q = 2) : d44471 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44579, d44471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44579, d44471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h11 p selected
theorem eqIntro37540 (p : Pattern) (selected : d44585 p = 2) : d44477 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44568 q = 2) : d44460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
    | true =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44569 q = 2) : d44461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44570 q = 2) : d44462 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44570, d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44570, d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44571 q = 2) : d44463 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44571, d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44571, d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44574 q = 2) : d44466 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44574, d44466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44574, d44466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44580 q = 2) : d44472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44580, d44472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37539 q selected
    | true =>
      simp only [d44580, d44472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44581 q = 2) : d44473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44581, d44473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44581, d44473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44582 q = 2) : d44474 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44582, d44474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44582, d44474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44583 q = 2) : d44475 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44583, d44475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44583, d44475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44584 q = 2) : d44476 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44584, d44476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44584, d44476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44585 q = 2) : d44477 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44585, d44477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44585, d44477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37541 (p : Pattern) (selected : d44592 p = 2) : d44484 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44576 q = 2) : d44468 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44576, d44468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37537 q selected
    | true =>
      simp only [d44576, d44468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37538 q selected
  have h2 (q : Pattern) (selected : d44577 q = 2) : d44469 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44577, d44469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44577, d44469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44578 q = 2) : d44470 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44578, d44470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44578, d44470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44586 q = 2) : d44478 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44586, d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37538 q selected
    | true =>
      simp only [d44586, d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37540 q selected
  have h5 (q : Pattern) (selected : d44587 q = 2) : d44479 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44587, d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44587, d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44588 q = 2) : d44480 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44588, d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44588, d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44589 q = 2) : d44481 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44589, d44481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44589, d44481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44590 q = 2) : d44482 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44590, d44482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44590, d44482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44591 q = 2) : d44483 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44591, d44483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44591, d44483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44592 q = 2) : d44484 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44592, d44484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44592, d44484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37542 (p : Pattern) (selected : d44596 p = 2) : d44488 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44586 q = 2) : d44478 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44586, d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37538 q selected
    | true =>
      simp only [d44586, d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37540 q selected
  have h2 (q : Pattern) (selected : d44587 q = 2) : d44479 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44587, d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44587, d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44588 q = 2) : d44480 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44588, d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44588, d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44590 q = 2) : d44482 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44590, d44482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44590, d44482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44595 q = 2) : d44487 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44595, d44487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44595, d44487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44596 q = 2) : d44488 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44596, d44488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44596, d44488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37543 (p : Pattern) (selected : d44602 p = 2) : d44494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44593 q = 2) : d44485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44593, d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37541 q selected
    | true =>
      simp only [d44593, d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44594 q = 2) : d44486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44594, d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44594, d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44597 q = 2) : d44489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44597, d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37542 q selected
    | true =>
      simp only [d44597, d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44598 q = 2) : d44490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44598, d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44598, d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44599 q = 2) : d44491 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44599, d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44599, d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44600 q = 2) : d44492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44600, d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44600, d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44601 q = 2) : d44493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44601, d44493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44601, d44493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44602 q = 2) : d44494 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44602, d44494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44602, d44494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37544 (p : Pattern) (selected : d44606 p = 2) : d44498 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44597 q = 2) : d44489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44597, d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37542 q selected
    | true =>
      simp only [d44597, d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44598 q = 2) : d44490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44598, d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44598, d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44603 q = 2) : d44495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44603, d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44603, d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44604 q = 2) : d44496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44604, d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44604, d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44605 q = 2) : d44497 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44605, d44497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44605, d44497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44606 q = 2) : d44498 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44606, d44498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44606, d44498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37545 (p : Pattern) (selected : d44609 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d35372 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d35372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro30479 q selected
  have h2 (q : Pattern) (selected : d10055 q = 2) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d10055, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro10598 q selected
  have h3 (q : Pattern) (selected : d35373 q = 2) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d35373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44441 q = 2) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44442 q = 2) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44443 q = 2) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44609 q = 2) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d44609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h7 p selected
theorem eqIntro37546 (p : Pattern) (selected : d44615 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44445 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44446 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44447 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44448 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44460 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44461 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44462 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44463 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44464 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44610 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37545 q selected
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44611 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44612 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44613 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d44614 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44615 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37547 (p : Pattern) (selected : d44616 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44610 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37545 q selected
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44611 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44612 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44613 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44614 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44616 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37548 (p : Pattern) (selected : d44622 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44468 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37515 q selected
    | true =>
      simp only [d44468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37516 q selected
  have h2 (q : Pattern) (selected : d44469 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44470 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44478 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37516 q selected
    | true =>
      simp only [d44478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37518 q selected
  have h5 (q : Pattern) (selected : d44479 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44480 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44481 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44617 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37546 q selected
    | true =>
      simp only [d44617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37547 q selected
  have h9 (q : Pattern) (selected : d44618 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44619 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44620 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44621 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44622 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro37549 (p : Pattern) (selected : d44628 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44623 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37548 q selected
    | true =>
      simp only [d44623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44624 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44625 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44626 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44627 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44628 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37550 (p : Pattern) (selected : d44634 p = 2) : d44504 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44522 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37527 q selected
    | true =>
      simp only [d44522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37528 q selected
  have h2 (q : Pattern) (selected : d44523 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44524 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44525 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44532 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37529 q selected
    | true =>
      simp only [d44532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37530 q selected
  have h6 (q : Pattern) (selected : d44533 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44534 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44548 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37533 q selected
    | true =>
      simp only [d44548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37521 q selected
  have h9 (q : Pattern) (selected : d44607 q = 2) : d44499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44607, d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37543 q selected
    | true =>
      simp only [d44607, d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37544 q selected
  have h10 (q : Pattern) (selected : d44608 q = 2) : d44500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44608, d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44608, d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44629 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37549 q selected
    | true =>
      simp only [d44629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44630 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44631 q = 2) : d44501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44631, d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44631, d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44632 q = 2) : d44502 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44632, d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44632, d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d44633 q = 2) : d44503 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44633, d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44633, d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d44634 q = 2) : d44504 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44634, d44504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44634, d44504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro37551 (p : Pattern) (selected : d44635 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44485 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37519 q selected
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44486 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44491 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44492 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44518 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44635 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37552 (p : Pattern) (selected : d44636 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44495 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44496 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44520 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44636 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37553 (p : Pattern) (selected : d44641 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44485 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37519 q selected
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44486 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44491 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44526 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44527 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44641 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37554 (p : Pattern) (selected : d44642 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44489 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37520 q selected
    | true =>
      simp only [d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44490 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44495 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44529 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44530 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44642 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37555 (p : Pattern) (selected : d44646 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44542 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37532 q selected
    | true =>
      simp only [d44542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44543 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44485 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37519 q selected
    | true =>
      simp only [d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44486 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44544 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44545 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44546 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44646 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37556 (p : Pattern) (selected : d44648 p = 2) : d44507 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44593 q = 2) : d44485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44593, d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37541 q selected
    | true =>
      simp only [d44593, d44485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44594 q = 2) : d44486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44594, d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44594, d44486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44597 q = 2) : d44489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44597, d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37542 q selected
    | true =>
      simp only [d44597, d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44598 q = 2) : d44490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44598, d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44598, d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44599 q = 2) : d44491 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44599, d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44599, d44491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44600 q = 2) : d44492 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44600, d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44600, d44492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44601 q = 2) : d44493 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44601, d44493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44601, d44493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44648 q = 2) : d44507 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44648, d44507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44648, d44507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37557 (p : Pattern) (selected : d44649 p = 2) : d44508 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44597 q = 2) : d44489 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44597, d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37542 q selected
    | true =>
      simp only [d44597, d44489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44598 q = 2) : d44490 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44598, d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44598, d44490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44603 q = 2) : d44495 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44603, d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44603, d44495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44604 q = 2) : d44496 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44604, d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44604, d44496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44605 q = 2) : d44497 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44605, d44497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44605, d44497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44649 q = 2) : d44508 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44649, d44508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44649, d44508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37558 (p : Pattern) (selected : d44652 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44623 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37548 q selected
    | true =>
      simp only [d44623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44624 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44625 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44626 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44627 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44652 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37559 (p : Pattern) (selected : d44658 p = 2) : d44514 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44522 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37527 q selected
    | true =>
      simp only [d44522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37528 q selected
  have h2 (q : Pattern) (selected : d44523 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44524 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44525 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44532 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37529 q selected
    | true =>
      simp only [d44532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37530 q selected
  have h6 (q : Pattern) (selected : d44533 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44534 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44548 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37533 q selected
    | true =>
      simp only [d44548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37521 q selected
  have h9 (q : Pattern) (selected : d44607 q = 2) : d44499 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44607, d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37543 q selected
    | true =>
      simp only [d44607, d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37544 q selected
  have h10 (q : Pattern) (selected : d44608 q = 2) : d44500 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44608, d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44608, d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44629 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37549 q selected
    | true =>
      simp only [d44629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44630 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44631 q = 2) : d44501 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44631, d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44631, d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44632 q = 2) : d44502 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44632, d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44632, d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d44633 q = 2) : d44503 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44633, d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44633, d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d44637 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37551 q selected
    | true =>
      simp only [d44637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37552 q selected
  have h17 (q : Pattern) (selected : d44638 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d44639 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d44639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d44640 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d44643 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37553 q selected
    | true =>
      simp only [d44643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37554 q selected
  have h21 (q : Pattern) (selected : d44644 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d44645 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d44645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d44647 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37555 q selected
    | true =>
      simp only [d44647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37524 q selected
  have h24 (q : Pattern) (selected : d44650 q = 2) : d44509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44650, d44509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37556 q selected
    | true =>
      simp only [d44650, d44509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37557 q selected
  have h25 (q : Pattern) (selected : d44651 q = 2) : d44510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44651, d44510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d44651, d44510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d44653 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37558 q selected
    | true =>
      simp only [d44653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d44654 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d44654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d44655 q = 2) : d44511 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44655, d44511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d44655, d44511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d44656 q = 2) : d44512 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44656, d44512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d44656, d44512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d44657 q = 2) : d44513 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44657, d44513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d44657, d44513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d44658 q = 2) : d44514 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44658, d44514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d44658, d44514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro37560 (p : Pattern) (selected : d44665 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44499 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37521 q selected
    | true =>
      simp only [d44499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37522 q selected
  have h2 (q : Pattern) (selected : d44500 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44501 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44502 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44503 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44660 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37522 q selected
    | true =>
      simp only [d44660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44661 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44662 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44663 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44664 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44665 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37561 (p : Pattern) (selected : d44671 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44660 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37522 q selected
    | true =>
      simp only [d44660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44661 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44662 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44663 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44664 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44666 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37525 q selected
    | true =>
      simp only [d44666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44667 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44668 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44669 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44670 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44671 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37562 (p : Pattern) (selected : d44678 p = 2) : d309695 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44647 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37555 q selected
    | true =>
      simp only [d44647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37524 q selected
  have h2 (q : Pattern) (selected : d44650 q = 2) : d44509 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44650, d44509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37556 q selected
    | true =>
      simp only [d44650, d44509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37557 q selected
  have h3 (q : Pattern) (selected : d44651 q = 2) : d44510 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44651, d44510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44651, d44510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44653 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37558 q selected
    | true =>
      simp only [d44653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44654 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44655 q = 2) : d44511 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44655, d44511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44655, d44511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44676 q = 2) : d44512 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44676, d44512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44676, d44512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44677 q = 2) : d44513 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44677, d44513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44677, d44513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44678 q = 2) : d309695 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44678, d309695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44678, d309695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37563 (p : Pattern) (selected : d44680 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44666 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37525 q selected
    | true =>
      simp only [d44666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44667 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44668 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44669 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44670 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44680 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37564 (p : Pattern) (selected : d44691 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44686 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
  have h2 (q : Pattern) (selected : d44445 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44687 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44446 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44688 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44689 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44690 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44691 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37565 (p : Pattern) (selected : d44697 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44686 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
  have h2 (q : Pattern) (selected : d44445 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44687 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44446 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44688 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44689 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44690 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44692 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
  have h9 (q : Pattern) (selected : d44460 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44693 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44461 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44694 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44695 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d44696 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d44697 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37566 (p : Pattern) (selected : d44702 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44686 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
  have h2 (q : Pattern) (selected : d44445 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44687 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44446 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44688 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44689 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44692 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
  have h8 (q : Pattern) (selected : d44460 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44693 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44461 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44694 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d44695 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44696 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44701 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44702 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37567 (p : Pattern) (selected : d44712 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44692 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
  have h2 (q : Pattern) (selected : d44460 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44693 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44461 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44694 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44695 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44701 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44707 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37517 q selected
  have h9 (q : Pattern) (selected : d44472 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37517 q selected
    | true =>
      simp only [d44472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44708 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44473 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44709 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44710 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d44711 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44712 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37568 (p : Pattern) (selected : d44718 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44698 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37564 q selected
    | true =>
      simp only [d44698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37565 q selected
  have h2 (q : Pattern) (selected : d44699 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44700 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44703 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37565 q selected
    | true =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37566 q selected
  have h5 (q : Pattern) (selected : d44704 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44705 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44706 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44713 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37566 q selected
    | true =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37567 q selected
  have h9 (q : Pattern) (selected : d44714 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44715 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44716 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d44717 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44718 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro37569 (p : Pattern) (selected : d44723 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44703 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37565 q selected
    | true =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37566 q selected
  have h2 (q : Pattern) (selected : d44704 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44705 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44713 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37566 q selected
    | true =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37567 q selected
  have h5 (q : Pattern) (selected : d44714 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44715 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44716 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44721 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44722 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44723 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37570 (p : Pattern) (selected : d44729 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44719 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37568 q selected
    | true =>
      simp only [d44719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44720 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44724 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37569 q selected
    | true =>
      simp only [d44724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44725 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44726 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44727 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44728 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44729 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37571 (p : Pattern) (selected : d44731 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44713 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37566 q selected
    | true =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37567 q selected
  have h2 (q : Pattern) (selected : d44714 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44715 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44721 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44730 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44731 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37572 (p : Pattern) (selected : d44737 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44724 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37569 q selected
    | true =>
      simp only [d44724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44725 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44732 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37571 q selected
    | true =>
      simp only [d44732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44733 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44734 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44735 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44736 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44737 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37573 (p : Pattern) (selected : d44749 p = 2) : d44697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44739 q = 2) : d44686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44739, d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44739, d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37534 q selected
  have h2 (q : Pattern) (selected : d44553 q = 2) : d44445 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44553, d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37534 q selected
    | true =>
      simp only [d44553, d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44740 q = 2) : d44687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44740, d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44740, d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44554 q = 2) : d44446 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44554, d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44554, d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44741 q = 2) : d44688 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44741, d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44741, d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44742 q = 2) : d44689 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44742, d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44742, d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44743 q = 2) : d44690 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44743, d44690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44743, d44690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44744 q = 2) : d44692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44744, d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44744, d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
  have h9 (q : Pattern) (selected : d44568 q = 2) : d44460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
    | true =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44745 q = 2) : d44693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44745, d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44745, d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44569 q = 2) : d44461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44746 q = 2) : d44694 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44746, d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44746, d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44747 q = 2) : d44695 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44747, d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44747, d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d44748 q = 2) : d44696 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44748, d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44748, d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d44749 q = 2) : d44697 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44749, d44697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44749, d44697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37574 (p : Pattern) (selected : d44751 p = 2) : d44702 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44739 q = 2) : d44686 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44739, d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44739, d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37534 q selected
  have h2 (q : Pattern) (selected : d44553 q = 2) : d44445 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44553, d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37534 q selected
    | true =>
      simp only [d44553, d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44740 q = 2) : d44687 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44740, d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44740, d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44554 q = 2) : d44446 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44554, d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44554, d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44741 q = 2) : d44688 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44741, d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44741, d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44742 q = 2) : d44689 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44742, d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44742, d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44744 q = 2) : d44692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44744, d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44744, d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
  have h8 (q : Pattern) (selected : d44568 q = 2) : d44460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
    | true =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44745 q = 2) : d44693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44745, d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44745, d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44569 q = 2) : d44461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44746 q = 2) : d44694 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44746, d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44746, d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d44747 q = 2) : d44695 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44747, d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44747, d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44748 q = 2) : d44696 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44748, d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44748, d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44750 q = 2) : d44701 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44750, d44701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44750, d44701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44751 q = 2) : d44702 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44751, d44702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44751, d44702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37575 (p : Pattern) (selected : d44760 p = 2) : d44712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44744 q = 2) : d44692 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44744, d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44744, d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
  have h2 (q : Pattern) (selected : d44568 q = 2) : d44460 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37536 q selected
    | true =>
      simp only [d44568, d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44745 q = 2) : d44693 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44745, d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44745, d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44569 q = 2) : d44461 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44569, d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44746 q = 2) : d44694 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44746, d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44746, d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44747 q = 2) : d44695 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44747, d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44747, d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44750 q = 2) : d44701 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44750, d44701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44750, d44701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44755 q = 2) : d44707 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44755, d44707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44755, d44707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37539 q selected
  have h9 (q : Pattern) (selected : d44580 q = 2) : d44472 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44580, d44472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37539 q selected
    | true =>
      simp only [d44580, d44472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44756 q = 2) : d44708 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44756, d44708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44756, d44708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44581 q = 2) : d44473 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44581, d44473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44581, d44473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44757 q = 2) : d44709 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44757, d44709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44757, d44709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44758 q = 2) : d44710 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44758, d44710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44758, d44710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d44759 q = 2) : d44711 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44759, d44711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44759, d44711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44760 q = 2) : d44712 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44760, d44712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44760, d44712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37576 (p : Pattern) (selected : d44767 p = 2) : d44723 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44752 q = 2) : d44703 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44752, d44703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37573 q selected
    | true =>
      simp only [d44752, d44703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37574 q selected
  have h2 (q : Pattern) (selected : d44753 q = 2) : d44704 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44753, d44704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44753, d44704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44754 q = 2) : d44705 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44754, d44705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44754, d44705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44761 q = 2) : d44713 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44761, d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37574 q selected
    | true =>
      simp only [d44761, d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37575 q selected
  have h5 (q : Pattern) (selected : d44762 q = 2) : d44714 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44762, d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44762, d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44763 q = 2) : d44715 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44763, d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44763, d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44764 q = 2) : d44716 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44764, d44716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44764, d44716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44765 q = 2) : d44721 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44765, d44721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44765, d44721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44766 q = 2) : d44722 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44766, d44722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44766, d44722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44767 q = 2) : d44723 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44767, d44723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44767, d44723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37577 (p : Pattern) (selected : d44771 p = 2) : d44731 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44761 q = 2) : d44713 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44761, d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37574 q selected
    | true =>
      simp only [d44761, d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37575 q selected
  have h2 (q : Pattern) (selected : d44762 q = 2) : d44714 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44762, d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44762, d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44763 q = 2) : d44715 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44763, d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44763, d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44765 q = 2) : d44721 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44765, d44721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44765, d44721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44770 q = 2) : d44730 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44770, d44730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44770, d44730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44771 q = 2) : d44731 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44771, d44731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44771, d44731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37578 (p : Pattern) (selected : d44777 p = 2) : d44737 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44768 q = 2) : d44724 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44768, d44724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37576 q selected
    | true =>
      simp only [d44768, d44724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44769 q = 2) : d44725 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44769, d44725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44769, d44725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44772 q = 2) : d44732 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44772, d44732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37577 q selected
    | true =>
      simp only [d44772, d44732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44773 q = 2) : d44733 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44773, d44733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44773, d44733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44774 q = 2) : d44734 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44774, d44734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44774, d44734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44775 q = 2) : d44735 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44775, d44735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44775, d44735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44776 q = 2) : d44736 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44776, d44736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44776, d44736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44777 q = 2) : d44737 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44777, d44737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44777, d44737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37579 (p : Pattern) (selected : d44781 p = 2) : d44813 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44772 q = 2) : d44732 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44772, d44732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37577 q selected
    | true =>
      simp only [d44772, d44732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44773 q = 2) : d44733 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44773, d44733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44773, d44733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44778 q = 2) : d44810 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44778, d44810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44778, d44810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44779 q = 2) : d44811 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44779, d44811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44779, d44811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44780 q = 2) : d44812 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44780, d44812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44780, d44812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44781 q = 2) : d44813 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44781, d44813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44781, d44813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37580 (p : Pattern) (selected : d44789 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44686 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
  have h2 (q : Pattern) (selected : d44445 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37512 q selected
    | true =>
      simp only [d44445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44687 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44446 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44688 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44689 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44692 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
  have h8 (q : Pattern) (selected : d44460 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37514 q selected
    | true =>
      simp only [d44460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d44693 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44461 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d44694 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d44694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d44695 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d44696 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44784 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37545 q selected
  have h15 (q : Pattern) (selected : d44610 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37545 q selected
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d44785 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d44611 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d44786 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d44787 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d44788 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d44789 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro37581 (p : Pattern) (selected : d44790 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44784 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37545 q selected
  have h2 (q : Pattern) (selected : d44610 q = 2) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37545 q selected
    | true =>
      simp only [d44610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44785 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44611 q = 2) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44786 q = 2) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44787 q = 2) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d44788 q = 2) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d44790 q = 2) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d44790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37582 (p : Pattern) (selected : d44796 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44703 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37565 q selected
    | true =>
      simp only [d44703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37566 q selected
  have h2 (q : Pattern) (selected : d44704 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44705 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44713 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37566 q selected
    | true =>
      simp only [d44713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37567 q selected
  have h5 (q : Pattern) (selected : d44714 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44715 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44716 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44791 q = 2) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d44791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37580 q selected
    | true =>
      simp only [d44791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37581 q selected
  have h9 (q : Pattern) (selected : d44792 q = 2) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d44792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44793 q = 2) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d44793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44794 q = 2) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d44794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d44795 q = 2) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d44795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d44795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44796 q = 2) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d44796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d44796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro37583 (p : Pattern) (selected : d44802 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44797 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37582 q selected
    | true =>
      simp only [d44797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44798 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44799 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44800 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44801 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44802 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37584 (p : Pattern) (selected : d44808 p = 2) : d309706 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44738 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37570 q selected
    | true =>
      simp only [d44738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37572 q selected
  have h2 (q : Pattern) (selected : d44782 q = 2) : d309701 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44782, d309701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37578 q selected
    | true =>
      simp only [d44782, d309701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37579 q selected
  have h3 (q : Pattern) (selected : d44783 q = 2) : d309702 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44783, d309702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44783, d309702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44803 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37583 q selected
    | true =>
      simp only [d44803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44804 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44805 q = 2) : d309703 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44805, d309703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44805, d309703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44806 q = 2) : d309704 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44806, d309704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44806, d309704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d44807 q = 2) : d309705 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44807, d309705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44807, d309705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44808 q = 2) : d309706 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44808, d309706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44808, d309706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37585 (p : Pattern) (selected : d44813 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44732 q = 2) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d44732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37571 q selected
    | true =>
      simp only [d44732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44733 q = 2) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d44733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44810 q = 2) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d44810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44811 q = 2) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d44811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44812 q = 2) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d44812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44813 q = 2) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d44813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37586 (p : Pattern) (selected : d44819 p = 2) : d0 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44814 q = 2) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d44814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37585 q selected
    | true =>
      simp only [d44814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44815 q = 2) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d44815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44816 q = 2) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d44816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44817 q = 2) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d44817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44818 q = 2) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d44818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44819 q = 2) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d44819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37587 (p : Pattern) (selected : d44825 p = 2) : d309712 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44505 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37523 q selected
  have h2 (q : Pattern) (selected : d44506 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44515 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37523 q selected
    | true =>
      simp only [d44515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37526 q selected
  have h4 (q : Pattern) (selected : d44516 q = 2) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44517 q = 2) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44659 q = 2) : d44515 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44659, d44515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37550 q selected
    | true =>
      simp only [d44659, d44515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37559 q selected
  have h7 (q : Pattern) (selected : d44672 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37560 q selected
    | true =>
      simp only [d44672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37561 q selected
  have h8 (q : Pattern) (selected : d44673 q = 2) : d44516 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44673, d44516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44673, d44516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44674 q = 2) : d309693 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44674, d309693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d44674, d309693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d44675 q = 2) : d309694 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44675, d309694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44675, d309694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44679 q = 2) : d309696 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44679, d309696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44679, d309696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37562 q selected
  have h12 (q : Pattern) (selected : d44681 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37563 q selected
  have h13 (q : Pattern) (selected : d44682 q = 2) : d309697 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44682, d309697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d44682, d309697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44683 q = 2) : d309698 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44683, d309698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d44683, d309698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d44684 q = 2) : d309699 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44684, d309699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d44684, d309699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d44685 q = 2) : d309700 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d44685, d309700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44685, d309700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d44809 q = 2) : d309707 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44809, d309707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44809, d309707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37584 q selected
  have h18 (q : Pattern) (selected : d44820 q = 2) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d44820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37586 q selected
  have h19 (q : Pattern) (selected : d44821 q = 2) : d309708 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d44821, d309708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d44821, d309708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d44822 q = 2) : d309709 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d44822, d309709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d44822, d309709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d44823 q = 2) : d309710 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d44823, d309710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d44823, d309710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d44824 q = 2) : d309711 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d44824, d309711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d44824, d309711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d44825 q = 2) : d309712 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d44825, d309712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d44825, d309712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro37588 (p : Pattern) (selected : d44831 p = 2) : d309718 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44826 q = 2) : d309713 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d44826, d309713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44826, d309713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37587 q selected
  have h2 (q : Pattern) (selected : d44827 q = 2) : d309714 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d44827, d309714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44827, d309714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d44828 q = 2) : d309715 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d44828, d309715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44828, d309715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d44829 q = 2) : d309716 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d44829, d309716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44829, d309716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d44830 q = 2) : d309717 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d44830, d309717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44830, d309717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d44831 q = 2) : d309718 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d44831, d309718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d44831, d309718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37589 (p : Pattern) (selected : d44837 p = 2) : d357556 p = 1 := by
  have h0 (q : Pattern) (selected : d42863 q = 2) : d357467 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d42863, d357467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37185 q selected
    | true =>
      simp only [d42863, d357467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37247 q selected
  have h1 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h2 (q : Pattern) (selected : d43276 q = 2) : d357494 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d43276, d357494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d43276, d357494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37325 q selected
  have h3 (q : Pattern) (selected : d43277 q = 2) : d357495 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d43277, d357495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d43277, d357495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d43840 q = 2) : d357522 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d43840, d357522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d43840, d357522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37415 q selected
  have h5 (q : Pattern) (selected : d43841 q = 2) : d357523 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d43841, d357523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d43841, d357523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d43842 q = 2) : d357524 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d43842, d357524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d43842, d357524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d44437 q = 2) : d357551 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d44437, d357551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44437, d357551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37511 q selected
  have h8 (q : Pattern) (selected : d44438 q = 2) : d357552 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d44438, d357552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44438, d357552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d44439 q = 2) : d357553 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d44439, d357553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44439, d357553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d44440 q = 2) : d357554 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d44440, d357554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d44440, d357554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d44832 q = 2) : d309719 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d44832, d309719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44832, d309719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37588 q selected
  have h12 (q : Pattern) (selected : d44833 q = 2) : d309720 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d44833, d309720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44833, d309720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d44834 q = 2) : d309721 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d44834, d309721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44834, d309721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d44835 q = 2) : d309722 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d44835, d309722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44835, d309722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d44836 q = 2) : d357555 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d44836, d357555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d44836, d357555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d44837 q = 2) : d357556 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d44837, d357556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d44837, d357556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h16 p selected
theorem eqIntro37590 (p : Pattern) (selected : d44843 p = 2) : d357562 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44838 q = 2) : d357557 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d44838, d357557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37589 q selected
    | true =>
      simp only [d44838, d357557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44839 q = 2) : d357558 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d44839, d357558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44839, d357558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44840 q = 2) : d357559 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d44840, d357559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44840, d357559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44841 q = 2) : d357560 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d44841, d357560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44841, d357560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44842 q = 2) : d357561 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d44842, d357561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44842, d357561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44843 q = 2) : d357562 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d44843, d357562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44843, d357562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37591 (p : Pattern) (selected : d44849 p = 2) : d357568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44844 q = 2) : d357563 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d44844, d357563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37590 q selected
    | true =>
      simp only [d44844, d357563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44845 q = 2) : d357564 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d44845, d357564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44845, d357564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44846 q = 2) : d357565 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d44846, d357565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44846, d357565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44847 q = 2) : d357566 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d44847, d357566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44847, d357566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44848 q = 2) : d357567 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d44848, d357567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44848, d357567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44849 q = 2) : d357568 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d44849, d357568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44849, d357568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37592 (p : Pattern) (selected : d44855 p = 2) : d357574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44850 q = 2) : d357569 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d44850, d357569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37591 q selected
    | true =>
      simp only [d44850, d357569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44851 q = 2) : d357570 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d44851, d357570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44851, d357570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44852 q = 2) : d357571 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d44852, d357571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44852, d357571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44853 q = 2) : d357572 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d44853, d357572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44853, d357572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44854 q = 2) : d357573 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d44854, d357573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44854, d357573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44855 q = 2) : d357574 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d44855, d357574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44855, d357574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37593 (p : Pattern) (selected : d44861 p = 2) : d357580 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44856 q = 2) : d357575 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d44856, d357575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37592 q selected
    | true =>
      simp only [d44856, d357575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44857 q = 2) : d357576 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d44857, d357576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44857, d357576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44858 q = 2) : d357577 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d44858, d357577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44858, d357577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44859 q = 2) : d357578 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d44859, d357578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44859, d357578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44860 q = 2) : d357579 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d44860, d357579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44860, d357579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44861 q = 2) : d357580 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d44861, d357580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44861, d357580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37594 (p : Pattern) (selected : d44867 p = 2) : d357586 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44862 q = 2) : d357581 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d44862, d357581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37593 q selected
    | true =>
      simp only [d44862, d357581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44863 q = 2) : d357582 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d44863, d357582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44863, d357582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44864 q = 2) : d357583 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d44864, d357583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44864, d357583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44865 q = 2) : d357584 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d44865, d357584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44865, d357584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44866 q = 2) : d357585 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d44866, d357585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44866, d357585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44867 q = 2) : d357586 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d44867, d357586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44867, d357586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37595 (p : Pattern) (selected : d44873 p = 2) : d357592 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44868 q = 2) : d357587 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d44868, d357587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37594 q selected
    | true =>
      simp only [d44868, d357587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44869 q = 2) : d357588 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d44869, d357588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44869, d357588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44870 q = 2) : d357589 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d44870, d357589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44870, d357589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44871 q = 2) : d357590 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d44871, d357590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44871, d357590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44872 q = 2) : d357591 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d44872, d357591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44872, d357591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44873 q = 2) : d357592 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d44873, d357592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44873, d357592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37596 (p : Pattern) (selected : d44879 p = 2) : d357598 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 2) : d0 q = 1 := by
    change (0 : Int) = 2 at selected
    omega
  have h1 (q : Pattern) (selected : d44874 q = 2) : d357593 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d44874, d357593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37595 q selected
    | true =>
      simp only [d44874, d357593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d44875 q = 2) : d357594 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d44875, d357594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d44875, d357594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d44876 q = 2) : d357595 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d44876, d357595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d44876, d357595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d44877 q = 2) : d357596 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d44877, d357596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d44877, d357596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d44878 q = 2) : d357597 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d44878, d357597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d44878, d357597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d44879 q = 2) : d357598 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d44879, d357598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d44879, d357598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37597 (p : Pattern) (selected : d358940 p = 0) : d361193 p = 1 := by
  have h0 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d271213 q = 0) : d271326 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271214 q = 0) : d273695 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d358938 q = 0) : d361191 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d358938, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358938, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d358939 q = 0) : d361192 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d358939, d361192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358939, d361192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d358940 q = 0) : d361193 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d358940, d361193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358940, d361193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro37598 (p : Pattern) (selected : d358946 p = 0) : d361199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358941 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37597 q selected
    | true =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358942 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358943 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358944 q = 0) : d361197 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d358944, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358944, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358945 q = 0) : d361198 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d358945, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358945, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d358946 q = 0) : d361199 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d358946, d361199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358946, d361199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37599 (p : Pattern) (selected : d358952 p = 0) : d361205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358947 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
    | true =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358948 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358949 q = 0) : d361202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d358949, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358949, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d358950 q = 0) : d361203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d358950, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358950, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358951 q = 0) : d361204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d358951, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358951, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d358952 q = 0) : d361205 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d358952, d361205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358952, d361205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37600 (p : Pattern) (selected : d358958 p = 0) : d361211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358953 q = 0) : d361206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d358953, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37599 q selected
    | true =>
      simp only [d358953, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358954 q = 0) : d361207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d358954, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358954, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358955 q = 0) : d361208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358955, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358955, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d358956 q = 0) : d361209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d358956, d361209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358956, d361209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358957 q = 0) : d361210 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d358957, d361210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358957, d361210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d358958 q = 0) : d361211 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d358958, d361211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358958, d361211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37601 (p : Pattern) (selected : d358964 p = 0) : d361217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358961 q = 0) : d361214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358962 q = 0) : d361215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d358962, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358962, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358963 q = 0) : d361216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d358963, d361216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358963, d361216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d358964 q = 0) : d361217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d358964, d361217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358964, d361217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37602 (p : Pattern) (selected : d358970 p = 0) : d361223 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358965 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
    | true =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358966 q = 0) : d361219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d358966, d361219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d358966, d361219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358967 q = 0) : d361220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d358967, d361220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358967, d361220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358968 q = 0) : d361221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d358968, d361221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358968, d361221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d358969 q = 0) : d361222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d358969, d361222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358969, d361222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358970 q = 0) : d361223 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d358970, d361223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358970, d361223, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37603 (p : Pattern) (selected : d358971 p = 0) : d361224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358961 q = 0) : d361214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358962 q = 0) : d361215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d358962, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358962, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358963 q = 0) : d361216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d358963, d361216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358963, d361216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d358971 q = 0) : d361224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d358971, d361224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358971, d361224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37604 (p : Pattern) (selected : d358977 p = 0) : d361230 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358965 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
    | true =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358966 q = 0) : d361219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d358966, d361219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d358966, d361219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358967 q = 0) : d361220 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d358967, d361220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358967, d361220, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358968 q = 0) : d361221 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d358968, d361221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358968, d361221, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d358969 q = 0) : d361222 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d358969, d361222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358969, d361222, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358972 q = 0) : d361225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
    | true =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358973 q = 0) : d361226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d358973, d361226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d358973, d361226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d358974 q = 0) : d361227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d358974, d361227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358974, d361227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358975 q = 0) : d361228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d358975, d361228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358975, d361228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d358976 q = 0) : d361229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d358976, d361229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358976, d361229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d358977 q = 0) : d361230 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d358977, d361230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358977, d361230, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37605 (p : Pattern) (selected : d358982 p = 0) : d361235 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358972 q = 0) : d361225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
    | true =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358973 q = 0) : d361226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d358973, d361226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d358973, d361226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358974 q = 0) : d361227 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d358974, d361227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358974, d361227, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358975 q = 0) : d361228 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d358975, d361228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358975, d361228, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d358976 q = 0) : d361229 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d358976, d361229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358976, d361229, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358982 q = 0) : d361235 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d358982, d361235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358982, d361235, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37606 (p : Pattern) (selected : d358993 p = 0) : d361246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358988 q = 0) : d361241 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358988, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358988, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
  have h2 (q : Pattern) (selected : d358947 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
    | true =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358989 q = 0) : d361242 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358989, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d358989, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d358948 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358990 q = 0) : d361243 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d358990, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358990, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358991 q = 0) : d361244 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d358991, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358991, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358992 q = 0) : d361245 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d358992, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d358992, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d358993 q = 0) : d361246 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d358993, d361246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358993, d361246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37607 (p : Pattern) (selected : d358999 p = 0) : d361252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358994 q = 0) : d361247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d358994, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37606 q selected
    | true =>
      simp only [d358994, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358995 q = 0) : d361248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d358995, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358995, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358996 q = 0) : d361249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358996, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358996, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d358997 q = 0) : d361250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d358997, d361250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358997, d361250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358998 q = 0) : d361251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d358998, d361251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358998, d361251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d358999 q = 0) : d361252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d358999, d361252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358999, d361252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37608 (p : Pattern) (selected : d359005 p = 0) : d361258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359000 q = 0) : d361253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359000, d361253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37607 q selected
    | true =>
      simp only [d359000, d361253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359001 q = 0) : d361254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359001, d361254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359001, d361254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359002 q = 0) : d361255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359002, d361255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359002, d361255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359003 q = 0) : d361256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359003, d361256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359003, d361256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359004 q = 0) : d361257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359004, d361257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359004, d361257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359005 q = 0) : d361258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359005, d361258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359005, d361258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37609 (p : Pattern) (selected : d359011 p = 0) : d361264 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359006 q = 0) : d361259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359006, d361259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37608 q selected
    | true =>
      simp only [d359006, d361259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359007 q = 0) : d361260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359007, d361260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359007, d361260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359008 q = 0) : d361261 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359008, d361261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359008, d361261, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359009 q = 0) : d361262 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359009, d361262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359009, d361262, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359010 q = 0) : d361263 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359010, d361263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359010, d361263, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359011 q = 0) : d361264 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359011, d361264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359011, d361264, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37610 (p : Pattern) (selected : d359017 p = 0) : d361270 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358978 q = 0) : d361231 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d358978, d361231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37602 q selected
    | true =>
      simp only [d358978, d361231, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37604 q selected
  have h2 (q : Pattern) (selected : d358979 q = 0) : d361232 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d358979, d361232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d358979, d361232, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358980 q = 0) : d361233 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d358980, d361233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358980, d361233, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358981 q = 0) : d361234 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d358981, d361234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358981, d361234, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d358983 q = 0) : d361236 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d358983, d361236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358983, d361236, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37605 q selected
  have h6 (q : Pattern) (selected : d358984 q = 0) : d361237 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d358984, d361237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358984, d361237, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358985 q = 0) : d361238 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d358985, d361238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d358985, d361238, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d358986 q = 0) : d361239 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d358986, d361239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358986, d361239, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358987 q = 0) : d361240 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d358987, d361240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358987, d361240, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359012 q = 0) : d361265 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359012, d361265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359012, d361265, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37609 q selected
  have h11 (q : Pattern) (selected : d359013 q = 0) : d361266 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359013, d361266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359013, d361266, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359014 q = 0) : d361267 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359014, d361267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359014, d361267, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359015 q = 0) : d361268 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359015, d361268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359015, d361268, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359016 q = 0) : d361269 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359016, d361269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359016, d361269, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359017 q = 0) : d361270 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d359017, d361270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359017, d361270, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37611 (p : Pattern) (selected : d359026 p = 0) : d361279 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358965 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
    | true =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359022 q = 0) : d361275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359022, d361275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359022, d361275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359023 q = 0) : d361276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359023, d361276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359023, d361276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359024 q = 0) : d361277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359024, d361277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359024, d361277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359025 q = 0) : d361278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359025, d361278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359025, d361278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359026 q = 0) : d361279 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359026, d361279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359026, d361279, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37612 (p : Pattern) (selected : d359033 p = 0) : d361286 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358965 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
    | true =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359022 q = 0) : d361275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359022, d361275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359022, d361275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359023 q = 0) : d361276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359023, d361276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359023, d361276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359024 q = 0) : d361277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359024, d361277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359024, d361277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359025 q = 0) : d361278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359025, d361278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359025, d361278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358972 q = 0) : d361225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
    | true =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359029 q = 0) : d361282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359029, d361282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359029, d361282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359030 q = 0) : d361283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359030, d361283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359030, d361283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359031 q = 0) : d361284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359031, d361284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359031, d361284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359032 q = 0) : d361285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359032, d361285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359032, d361285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359033 q = 0) : d361286 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359033, d361286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359033, d361286, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37613 (p : Pattern) (selected : d359038 p = 0) : d361291 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358961 q = 0) : d361214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358962 q = 0) : d361215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d358962, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358962, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359037 q = 0) : d361290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359037, d361290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359037, d361290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359038 q = 0) : d361291 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359038, d361291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359038, d361291, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37614 (p : Pattern) (selected : d359045 p = 0) : d361298 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358961 q = 0) : d361214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359043 q = 0) : d361296 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359043, d361296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359043, d361296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359044 q = 0) : d361297 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359044, d361297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359044, d361297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359045 q = 0) : d361298 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359045, d361298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359045, d361298, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37615 (p : Pattern) (selected : d359051 p = 0) : d361304 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d271326 q = 0) : d271213 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271326, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d271326, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271213 q = 0) : d271326 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d271327 q = 0) : d273807 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271327, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271327, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d271214 q = 0) : d273695 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359049 q = 0) : d361302 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359049, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359049, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d358938 q = 0) : d361191 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d358938, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358938, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359050 q = 0) : d361303 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359050, d361303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359050, d361303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d358939 q = 0) : d361192 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d358939, d361192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358939, d361192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359051 q = 0) : d361304 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359051, d361304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359051, d361304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro37616 (p : Pattern) (selected : d359057 p = 0) : d361310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359052 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37615 q selected
    | true =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359053 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358941 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37597 q selected
    | true =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358942 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359054 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358943 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359055 q = 0) : d361308 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359055, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359055, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359056 q = 0) : d361309 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359056, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359056, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358944 q = 0) : d361197 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d358944, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d358944, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d358945 q = 0) : d361198 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d358945, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d358945, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359057 q = 0) : d361310 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359057, d361310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359057, d361310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37617 (p : Pattern) (selected : d359063 p = 0) : d361316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359058 q = 0) : d361311 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359058, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37616 q selected
    | true =>
      simp only [d359058, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359059 q = 0) : d361312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359059, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359059, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359060 q = 0) : d361313 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359060, d361313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359060, d361313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359061 q = 0) : d361314 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359061, d361314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359061, d361314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358947 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
    | true =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d358948 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358949 q = 0) : d361202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d358949, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358949, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d358950 q = 0) : d361203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d358950, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358950, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359062 q = 0) : d361315 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359062, d361315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359062, d361315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d358951 q = 0) : d361204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d358951, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d358951, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359063 q = 0) : d361316 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359063, d361316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359063, d361316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37618 (p : Pattern) (selected : d359069 p = 0) : d361322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359064 q = 0) : d361317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37617 q selected
    | true =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37599 q selected
  have h2 (q : Pattern) (selected : d359065 q = 0) : d361318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359066 q = 0) : d361319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d358953 q = 0) : d361206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d358953, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37599 q selected
    | true =>
      simp only [d358953, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358954 q = 0) : d361207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d358954, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358954, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358955 q = 0) : d361208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358955, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358955, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359067 q = 0) : d361320 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359067, d361320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359067, d361320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d358956 q = 0) : d361209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d358956, d361209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d358956, d361209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359068 q = 0) : d361321 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359068, d361321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359068, d361321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359069 q = 0) : d361322 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359069, d361322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359069, d361322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37619 (p : Pattern) (selected : d359075 p = 0) : d361328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359072 q = 0) : d361325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359073 q = 0) : d361326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359073, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359073, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359074 q = 0) : d361327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359074, d361327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359074, d361327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359075 q = 0) : d361328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359075, d361328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359075, d361328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37620 (p : Pattern) (selected : d359079 p = 0) : d361193 p = 1 := by
  have h0 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h1 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h2 (q : Pattern) (selected : d271355 q = 0) : d271326 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d271355, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271356 q = 0) : d273695 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271356, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h4 (q : Pattern) (selected : d359077 q = 0) : d361191 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359077, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h5 (q : Pattern) (selected : d359078 q = 0) : d361192 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359078, d361192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359078, d361192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d359079 q = 0) : d361193 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359079, d361193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359079, d361193, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  exact h6 p selected
theorem eqIntro37621 (p : Pattern) (selected : d359085 p = 0) : d361199 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359080 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37620 q selected
    | true =>
      simp only [d359080, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359081 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359081, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359082 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359082, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359083 q = 0) : d361197 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359083, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359083, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359084 q = 0) : d361198 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359084, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359084, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359085 q = 0) : d361199 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359085, d361199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359085, d361199, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37622 (p : Pattern) (selected : d359091 p = 0) : d361205 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359086 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
    | true =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359087 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359088 q = 0) : d361202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359088, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359088, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359089 q = 0) : d361203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359089, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359089, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359090 q = 0) : d361204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359090, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359090, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359091 q = 0) : d361205 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359091, d361205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359091, d361205, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37623 (p : Pattern) (selected : d359097 p = 0) : d361211 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359092 q = 0) : d361206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359092, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37622 q selected
    | true =>
      simp only [d359092, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359093 q = 0) : d361207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359093, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359093, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359094 q = 0) : d361208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359094, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359094, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359095 q = 0) : d361209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359095, d361209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359095, d361209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359096 q = 0) : d361210 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359096, d361210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359096, d361210, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359097 q = 0) : d361211 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359097, d361211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359097, d361211, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37624 (p : Pattern) (selected : d359103 p = 0) : d361217 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359098 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359098, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37623 q selected
    | true =>
      simp only [d359098, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359099 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359099, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359099, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359100 q = 0) : d361214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359100, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359100, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359101 q = 0) : d361215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359101, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359101, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359102 q = 0) : d361216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359102, d361216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359102, d361216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359103 q = 0) : d361217 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359103, d361217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359103, d361217, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37625 (p : Pattern) (selected : d359109 p = 0) : d361334 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359039 q = 0) : d361292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359039, d361292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37613 q selected
    | true =>
      simp only [d359039, d361292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359040 q = 0) : d361293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359040, d361293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359040, d361293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359041 q = 0) : d361294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359041, d361294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359041, d361294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359042 q = 0) : d361295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359042, d361295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359042, d361295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359046 q = 0) : d361299 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359046, d361299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37614 q selected
    | true =>
      simp only [d359046, d361299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359047 q = 0) : d361300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359047, d361300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359047, d361300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359048 q = 0) : d361301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359048, d361301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359048, d361301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359076 q = 0) : d361329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37619 q selected
    | true =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
  have h9 (q : Pattern) (selected : d359104 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359104, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37624 q selected
    | true =>
      simp only [d359104, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359105 q = 0) : d361330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359105, d361330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359105, d361330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d358965 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
    | true =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d358966 q = 0) : d361219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d358966, d361219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d358966, d361219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359106 q = 0) : d361331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359106, d361331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359106, d361331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359107 q = 0) : d361332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359107, d361332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359107, d361332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359108 q = 0) : d361333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359108, d361333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359108, d361333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359109 q = 0) : d361334 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359109, d361334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359109, d361334, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro37626 (p : Pattern) (selected : d359110 p = 0) : d361335 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358961 q = 0) : d361214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358962 q = 0) : d361215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d358962, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358962, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359037 q = 0) : d361290 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359037, d361290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359037, d361290, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359110 q = 0) : d361335 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359110, d361335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359110, d361335, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37627 (p : Pattern) (selected : d359115 p = 0) : d361340 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358961 q = 0) : d361214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d358961, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359043 q = 0) : d361296 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359043, d361296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359043, d361296, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359044 q = 0) : d361297 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359044, d361297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359044, d361297, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359115 q = 0) : d361340 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359115, d361340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359115, d361340, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37628 (p : Pattern) (selected : d359119 p = 0) : d361344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359072 q = 0) : d361325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359073 q = 0) : d361326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359073, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359073, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359074 q = 0) : d361327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359074, d361327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359074, d361327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359119 q = 0) : d361344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359119, d361344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359119, d361344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37629 (p : Pattern) (selected : d359121 p = 0) : d361224 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359098 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359098, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37623 q selected
    | true =>
      simp only [d359098, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359099 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359099, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359099, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359100 q = 0) : d361214 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359100, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359100, d361214, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359101 q = 0) : d361215 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359101, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359101, d361215, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359102 q = 0) : d361216 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359102, d361216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359102, d361216, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359121 q = 0) : d361224 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359121, d361224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359121, d361224, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37630 (p : Pattern) (selected : d359127 p = 0) : d361350 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359039 q = 0) : d361292 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359039, d361292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37613 q selected
    | true =>
      simp only [d359039, d361292, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359040 q = 0) : d361293 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359040, d361293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359040, d361293, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359041 q = 0) : d361294 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359041, d361294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359041, d361294, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359042 q = 0) : d361295 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359042, d361295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359042, d361295, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359046 q = 0) : d361299 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359046, d361299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37614 q selected
    | true =>
      simp only [d359046, d361299, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359047 q = 0) : d361300 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359047, d361300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359047, d361300, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359048 q = 0) : d361301 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359048, d361301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359048, d361301, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359076 q = 0) : d361329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37619 q selected
    | true =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
  have h9 (q : Pattern) (selected : d359104 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359104, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37624 q selected
    | true =>
      simp only [d359104, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359105 q = 0) : d361330 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359105, d361330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359105, d361330, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d358965 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
    | true =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d358966 q = 0) : d361219 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d358966, d361219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d358966, d361219, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359106 q = 0) : d361331 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359106, d361331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359106, d361331, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359107 q = 0) : d361332 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359107, d361332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359107, d361332, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359108 q = 0) : d361333 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359108, d361333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359108, d361333, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359111 q = 0) : d361336 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359111, d361336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37626 q selected
    | true =>
      simp only [d359111, d361336, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h17 (q : Pattern) (selected : d359112 q = 0) : d361337 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359112, d361337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359112, d361337, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359113 q = 0) : d361338 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359113, d361338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359113, d361338, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d359114 q = 0) : d361339 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359114, d361339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359114, d361339, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d359116 q = 0) : d361341 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359116, d361341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37627 q selected
    | true =>
      simp only [d359116, d361341, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d359117 q = 0) : d361342 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359117, d361342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359117, d361342, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d359118 q = 0) : d361343 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359118, d361343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359118, d361343, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d359120 q = 0) : d361345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359120, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37628 q selected
    | true =>
      simp only [d359120, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
  have h24 (q : Pattern) (selected : d359122 q = 0) : d361225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359122, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37629 q selected
    | true =>
      simp only [d359122, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h25 (q : Pattern) (selected : d359123 q = 0) : d361346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359123, d361346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d359123, d361346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d358972 q = 0) : d361225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
    | true =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d358973 q = 0) : d361226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d358973, d361226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d358973, d361226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d359124 q = 0) : d361347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359124, d361347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d359124, d361347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d359125 q = 0) : d361348 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359125, d361348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d359125, d361348, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d359126 q = 0) : d361349 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359126, d361349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359126, d361349, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d359127 q = 0) : d361350 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359127, d361350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359127, d361350, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro37631 (p : Pattern) (selected : d359129 p = 0) : d361352 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358965 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
    | true =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359022 q = 0) : d361275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359022, d361275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359022, d361275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359023 q = 0) : d361276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359023, d361276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359023, d361276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359024 q = 0) : d361277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359024, d361277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359024, d361277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359025 q = 0) : d361278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359025, d361278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359025, d361278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359129 q = 0) : d361352 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359129, d361352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359129, d361352, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37632 (p : Pattern) (selected : d359136 p = 0) : d361359 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359120 q = 0) : d361345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359120, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37628 q selected
    | true =>
      simp only [d359120, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
  have h2 (q : Pattern) (selected : d359122 q = 0) : d361225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359122, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37629 q selected
    | true =>
      simp only [d359122, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359123 q = 0) : d361346 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359123, d361346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359123, d361346, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d358972 q = 0) : d361225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
    | true =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358973 q = 0) : d361226 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d358973, d361226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358973, d361226, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359124 q = 0) : d361347 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359124, d361347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359124, d361347, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359134 q = 0) : d361357 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359134, d361357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359134, d361357, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359135 q = 0) : d361358 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359135, d361358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359135, d361358, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359136 q = 0) : d361359 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359136, d361359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359136, d361359, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37633 (p : Pattern) (selected : d359147 p = 0) : d361370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359142 q = 0) : d361365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359142, d361365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359142, d361365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37616 q selected
  have h2 (q : Pattern) (selected : d359058 q = 0) : d361311 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359058, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37616 q selected
    | true =>
      simp only [d359058, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359143 q = 0) : d361366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359143, d361366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359143, d361366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359059 q = 0) : d361312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359059, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359059, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359144 q = 0) : d361367 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359144, d361367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359144, d361367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359145 q = 0) : d361368 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359145, d361368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359145, d361368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358988 q = 0) : d361241 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358988, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358988, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
  have h8 (q : Pattern) (selected : d358947 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
    | true =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358989 q = 0) : d361242 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358989, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358989, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d358948 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d358990 q = 0) : d361243 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d358990, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d358990, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d358991 q = 0) : d361244 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d358991, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d358991, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359146 q = 0) : d361369 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359146, d361369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359146, d361369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d358992 q = 0) : d361245 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d358992, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d358992, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359147 q = 0) : d361370 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359147, d361370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359147, d361370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37634 (p : Pattern) (selected : d359153 p = 0) : d361376 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359148 q = 0) : d361371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37633 q selected
    | true =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37606 q selected
  have h2 (q : Pattern) (selected : d359149 q = 0) : d361372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359150 q = 0) : d361373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d358994 q = 0) : d361247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d358994, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37606 q selected
    | true =>
      simp only [d358994, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358995 q = 0) : d361248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d358995, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358995, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358996 q = 0) : d361249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358996, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358996, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359151 q = 0) : d361374 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359151, d361374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359151, d361374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d358997 q = 0) : d361250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d358997, d361250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d358997, d361250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359152 q = 0) : d361375 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359152, d361375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359152, d361375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359153 q = 0) : d361376 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359153, d361376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359153, d361376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37635 (p : Pattern) (selected : d359159 p = 0) : d361382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359154 q = 0) : d361377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359154, d361377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37634 q selected
    | true =>
      simp only [d359154, d361377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359155 q = 0) : d361378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359155, d361378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359155, d361378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359000 q = 0) : d361253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359000, d361253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37607 q selected
    | true =>
      simp only [d359000, d361253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359001 q = 0) : d361254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359001, d361254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359001, d361254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359156 q = 0) : d361379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359156, d361379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359156, d361379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359157 q = 0) : d361380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359157, d361380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359157, d361380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359158 q = 0) : d361381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359158, d361381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359158, d361381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359159 q = 0) : d361382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359159, d361382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359159, d361382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37636 (p : Pattern) (selected : d359166 p = 0) : d361246 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359161 q = 0) : d361241 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359161, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359161, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
  have h2 (q : Pattern) (selected : d359086 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
    | true =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359162 q = 0) : d361242 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359162, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359162, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359087 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359163 q = 0) : d361243 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359163, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359163, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359164 q = 0) : d361244 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359164, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359164, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359165 q = 0) : d361245 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359165, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359165, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359166 q = 0) : d361246 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359166, d361246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359166, d361246, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37637 (p : Pattern) (selected : d359172 p = 0) : d361252 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359167 q = 0) : d361247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359167, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37636 q selected
    | true =>
      simp only [d359167, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359168 q = 0) : d361248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359168, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359168, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359169 q = 0) : d361249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359169, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359169, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359170 q = 0) : d361250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359170, d361250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359170, d361250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359171 q = 0) : d361251 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359171, d361251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359171, d361251, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359172 q = 0) : d361252 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359172, d361252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359172, d361252, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37638 (p : Pattern) (selected : d359178 p = 0) : d361258 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359173 q = 0) : d361253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359173, d361253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37637 q selected
    | true =>
      simp only [d359173, d361253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359174 q = 0) : d361254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359174, d361254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359174, d361254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359175 q = 0) : d361255 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359175, d361255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359175, d361255, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359176 q = 0) : d361256 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359176, d361256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359176, d361256, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359177 q = 0) : d361257 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359177, d361257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359177, d361257, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359178 q = 0) : d361258 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359178, d361258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359178, d361258, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37639 (p : Pattern) (selected : d359184 p = 0) : d361388 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359160 q = 0) : d361383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359160, d361383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37635 q selected
    | true =>
      simp only [d359160, d361383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37608 q selected
  have h2 (q : Pattern) (selected : d359179 q = 0) : d361259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359179, d361259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37638 q selected
    | true =>
      simp only [d359179, d361259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359180 q = 0) : d361384 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359180, d361384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359180, d361384, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359006 q = 0) : d361259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359006, d361259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37608 q selected
    | true =>
      simp only [d359006, d361259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359007 q = 0) : d361260 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359007, d361260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359007, d361260, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359181 q = 0) : d361385 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359181, d361385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359181, d361385, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359182 q = 0) : d361386 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359182, d361386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359182, d361386, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359183 q = 0) : d361387 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359183, d361387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359183, d361387, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359184 q = 0) : d361388 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359184, d361388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359184, d361388, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37640 (p : Pattern) (selected : d359190 p = 0) : d361394 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359027 q = 0) : d361280 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359027, d361280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359027, d361280, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37611 q selected
  have h2 (q : Pattern) (selected : d359028 q = 0) : d361281 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359028, d361281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359028, d361281, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359034 q = 0) : d361287 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359034, d361287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37611 q selected
    | true =>
      simp only [d359034, d361287, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37612 q selected
  have h4 (q : Pattern) (selected : d359035 q = 0) : d361288 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359035, d361288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359035, d361288, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359036 q = 0) : d361289 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359036, d361289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359036, d361289, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359128 q = 0) : d361351 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359128, d361351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37625 q selected
    | true =>
      simp only [d359128, d361351, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37630 q selected
  have h7 (q : Pattern) (selected : d359130 q = 0) : d361353 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359130, d361353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37631 q selected
    | true =>
      simp only [d359130, d361353, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359131 q = 0) : d361354 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359131, d361354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359131, d361354, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359132 q = 0) : d361355 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359132, d361355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359132, d361355, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359133 q = 0) : d361356 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359133, d361356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359133, d361356, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359137 q = 0) : d361360 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359137, d361360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359137, d361360, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37632 q selected
  have h12 (q : Pattern) (selected : d359138 q = 0) : d361361 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359138, d361361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359138, d361361, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359139 q = 0) : d361362 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359139, d361362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359139, d361362, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359140 q = 0) : d361363 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359140, d361363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359140, d361363, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359141 q = 0) : d361364 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359141, d361364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359141, d361364, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359185 q = 0) : d361389 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359185, d361389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359185, d361389, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37639 q selected
  have h17 (q : Pattern) (selected : d359186 q = 0) : d361390 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359186, d361390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359186, d361390, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359187 q = 0) : d361391 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359187, d361391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359187, d361391, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d359188 q = 0) : d361392 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359188, d361392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d359188, d361392, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d359189 q = 0) : d361393 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359189, d361393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359189, d361393, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d359190 q = 0) : d361394 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d359190, d361394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359190, d361394, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  exact h21 p selected
theorem eqIntro37641 (p : Pattern) (selected : d359200 p = 0) : d361404 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359076 q = 0) : d361329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37619 q selected
    | true =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
  have h2 (q : Pattern) (selected : d359196 q = 0) : d361400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359196, d361400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359196, d361400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359197 q = 0) : d361401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359197, d361401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359197, d361401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359198 q = 0) : d361402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359198, d361402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359198, d361402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359199 q = 0) : d361403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359199, d361403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359199, d361403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359200 q = 0) : d361404 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359200, d361404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359200, d361404, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37642 (p : Pattern) (selected : d359207 p = 0) : d361411 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359076 q = 0) : d361329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37619 q selected
    | true =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
  have h2 (q : Pattern) (selected : d359196 q = 0) : d361400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359196, d361400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359196, d361400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359197 q = 0) : d361401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359197, d361401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359197, d361401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359198 q = 0) : d361402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359198, d361402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359198, d361402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359199 q = 0) : d361403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359199, d361403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359199, d361403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359120 q = 0) : d361345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359120, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37628 q selected
    | true =>
      simp only [d359120, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
  have h7 (q : Pattern) (selected : d359203 q = 0) : d361407 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359203, d361407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359203, d361407, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359204 q = 0) : d361408 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359204, d361408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359204, d361408, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359205 q = 0) : d361409 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359205, d361409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359205, d361409, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359206 q = 0) : d361410 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359206, d361410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359206, d361410, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359207 q = 0) : d361411 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359207, d361411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359207, d361411, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37643 (p : Pattern) (selected : d359212 p = 0) : d361416 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359072 q = 0) : d361325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359073 q = 0) : d361326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359073, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359073, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359211 q = 0) : d361415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359211, d361415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359211, d361415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359212 q = 0) : d361416 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359212, d361416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359212, d361416, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37644 (p : Pattern) (selected : d359219 p = 0) : d361423 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359072 q = 0) : d361325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359217 q = 0) : d361421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359217, d361421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359217, d361421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359218 q = 0) : d361422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359218, d361422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359218, d361422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359219 q = 0) : d361423 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359219, d361423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359219, d361423, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37645 (p : Pattern) (selected : d359225 p = 0) : d361429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d271213 q = 0) : d271326 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272403 q = 0) : d274587 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272403, d274587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272403, d274587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359223 q = 0) : d361427 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359223, d361427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359223, d361427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d271326 q = 0) : d271213 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271326, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d271326, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d271327 q = 0) : d273807 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271327, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d271327, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d271214 q = 0) : d273695 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359049 q = 0) : d361302 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359049, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359049, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359224 q = 0) : d361428 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359224, d361428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359224, d361428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d358938 q = 0) : d361191 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d358938, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358938, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359050 q = 0) : d361303 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359050, d361303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359050, d361303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359225 q = 0) : d361429 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359225, d361429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359225, d361429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro37646 (p : Pattern) (selected : d359231 p = 0) : d361435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359226 q = 0) : d361430 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359226, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37645 q selected
    | true =>
      simp only [d359226, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359227 q = 0) : d361431 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359227, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359227, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359052 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37615 q selected
    | true =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359053 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359228 q = 0) : d361432 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359228, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359228, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358941 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37597 q selected
    | true =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358942 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359054 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359229 q = 0) : d361433 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359229, d361433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359229, d361433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359230 q = 0) : d361434 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359230, d361434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359230, d361434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d358943 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359055 q = 0) : d361308 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359055, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359055, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359056 q = 0) : d361309 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359056, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359056, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359231 q = 0) : d361435 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359231, d361435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359231, d361435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro37647 (p : Pattern) (selected : d359239 p = 0) : d361443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359052 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37615 q selected
    | true =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359053 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358941 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37597 q selected
    | true =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358942 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359054 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359237 q = 0) : d361441 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359237, d361441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359237, d361441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359238 q = 0) : d361442 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359238, d361442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359238, d361442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d358943 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358944 q = 0) : d361197 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d358944, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d358944, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d358945 q = 0) : d361198 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d358945, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d358945, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359239 q = 0) : d361443 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359239, d361443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359239, d361443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37648 (p : Pattern) (selected : d359245 p = 0) : d361449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359232 q = 0) : d361436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359232, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37646 q selected
    | true =>
      simp only [d359232, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359233 q = 0) : d361437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359233, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359233, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359234 q = 0) : d361438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359234, d361438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359234, d361438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359235 q = 0) : d361439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359235, d361439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359235, d361439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359058 q = 0) : d361311 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359058, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37616 q selected
    | true =>
      simp only [d359058, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359059 q = 0) : d361312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359059, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359059, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359060 q = 0) : d361313 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359060, d361313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359060, d361313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359061 q = 0) : d361314 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359061, d361314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359061, d361314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359236 q = 0) : d361440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359236, d361440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359236, d361440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359240 q = 0) : d361444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
    | true =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359241 q = 0) : d361445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359242 q = 0) : d361446 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359242, d361446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359242, d361446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359243 q = 0) : d361447 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359243, d361447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359243, d361447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d358947 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
    | true =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d358948 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d358949 q = 0) : d361202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d358949, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358949, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d358950 q = 0) : d361203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d358950, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d358950, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359244 q = 0) : d361448 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359244, d361448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359244, d361448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359245 q = 0) : d361449 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359245, d361449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359245, d361449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro37649 (p : Pattern) (selected : d359251 p = 0) : d361455 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359246 q = 0) : d361450 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359246, d361450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37648 q selected
    | true =>
      simp only [d359246, d361450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37617 q selected
  have h2 (q : Pattern) (selected : d359247 q = 0) : d361451 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359247, d361451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359247, d361451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359248 q = 0) : d361452 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359248, d361452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359248, d361452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359064 q = 0) : d361317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37617 q selected
    | true =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37599 q selected
  have h5 (q : Pattern) (selected : d359065 q = 0) : d361318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359066 q = 0) : d361319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359249 q = 0) : d361453 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359249, d361453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359249, d361453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d358953 q = 0) : d361206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d358953, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37599 q selected
    | true =>
      simp only [d358953, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358954 q = 0) : d361207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d358954, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358954, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d358955 q = 0) : d361208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358955, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358955, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359067 q = 0) : d361320 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359067, d361320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359067, d361320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359250 q = 0) : d361454 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359250, d361454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359250, d361454, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359251 q = 0) : d361455 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359251, d361455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359251, d361455, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro37650 (p : Pattern) (selected : d359257 p = 0) : d361461 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359252 q = 0) : d361456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359252, d361456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37649 q selected
    | true =>
      simp only [d359252, d361456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359253 q = 0) : d361457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359253, d361457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359253, d361457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359254 q = 0) : d361458 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359254, d361458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359254, d361458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359255 q = 0) : d361459 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359255, d361459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359255, d361459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359256 q = 0) : d361460 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359256, d361460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359256, d361460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359257 q = 0) : d361461 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359257, d361461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359257, d361461, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37651 (p : Pattern) (selected : d359261 p = 0) : d361304 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d49282 q = 0) : d271213 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d49282, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d49282, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271355 q = 0) : d271326 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d271538 q = 0) : d273807 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271538, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271538, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d271356 q = 0) : d273695 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d271356, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359259 q = 0) : d361302 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359259, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359259, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359077 q = 0) : d361191 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359077, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359260 q = 0) : d361303 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359260, d361303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359260, d361303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359078 q = 0) : d361192 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359078, d361192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359078, d361192, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359261 q = 0) : d361304 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359261, d361304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359261, d361304, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  exact h10 p selected
theorem eqIntro37652 (p : Pattern) (selected : d359267 p = 0) : d361310 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359262 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37651 q selected
    | true =>
      simp only [d359262, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359263 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359263, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359080 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37620 q selected
    | true =>
      simp only [d359080, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359081 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359081, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359264 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359264, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359082 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359082, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359265 q = 0) : d361308 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359265, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359265, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359266 q = 0) : d361309 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359266, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359266, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359083 q = 0) : d361197 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359083, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359083, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359084 q = 0) : d361198 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359084, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359084, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359267 q = 0) : d361310 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359267, d361310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359267, d361310, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37653 (p : Pattern) (selected : d359273 p = 0) : d361316 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359268 q = 0) : d361311 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359268, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37652 q selected
    | true =>
      simp only [d359268, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359269 q = 0) : d361312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359269, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359269, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359270 q = 0) : d361313 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359270, d361313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359270, d361313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359271 q = 0) : d361314 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359271, d361314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359271, d361314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359086 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
    | true =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359087 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359088 q = 0) : d361202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359088, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359088, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359089 q = 0) : d361203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359089, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359089, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359272 q = 0) : d361315 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359272, d361315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359272, d361315, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359090 q = 0) : d361204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359090, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359090, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359273 q = 0) : d361316 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359273, d361316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359273, d361316, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37654 (p : Pattern) (selected : d359279 p = 0) : d361322 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359274 q = 0) : d361317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359274, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37653 q selected
    | true =>
      simp only [d359274, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37622 q selected
  have h2 (q : Pattern) (selected : d359275 q = 0) : d361318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359275, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359275, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359276 q = 0) : d361319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359276, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359276, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359092 q = 0) : d361206 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359092, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37622 q selected
    | true =>
      simp only [d359092, d361206, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359093 q = 0) : d361207 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359093, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359093, d361207, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359094 q = 0) : d361208 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359094, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359094, d361208, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359277 q = 0) : d361320 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359277, d361320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359277, d361320, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359095 q = 0) : d361209 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359095, d361209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359095, d361209, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359278 q = 0) : d361321 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359278, d361321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359278, d361321, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359279 q = 0) : d361322 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359279, d361322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359279, d361322, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37655 (p : Pattern) (selected : d359285 p = 0) : d361328 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359280 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359280, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37654 q selected
    | true =>
      simp only [d359280, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359281 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359281, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359281, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359098 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359098, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37623 q selected
    | true =>
      simp only [d359098, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359099 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359099, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359099, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359282 q = 0) : d361325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359282, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359282, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359283 q = 0) : d361326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359283, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359283, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359284 q = 0) : d361327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359284, d361327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359284, d361327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359285 q = 0) : d361328 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359285, d361328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359285, d361328, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37656 (p : Pattern) (selected : d359291 p = 0) : d361467 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359288 q = 0) : d361464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359288, d361464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359288, d361464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359289 q = 0) : d361465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359289, d361465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359289, d361465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359290 q = 0) : d361466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359290, d361466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359290, d361466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359291 q = 0) : d361467 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359291, d361467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359291, d361467, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37657 (p : Pattern) (selected : d359297 p = 0) : d361473 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359213 q = 0) : d361417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359213, d361417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37643 q selected
    | true =>
      simp only [d359213, d361417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37613 q selected
  have h2 (q : Pattern) (selected : d359214 q = 0) : d361418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359214, d361418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359214, d361418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359215 q = 0) : d361419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359215, d361419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359215, d361419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359216 q = 0) : d361420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359216, d361420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359216, d361420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359220 q = 0) : d361424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359220, d361424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37644 q selected
    | true =>
      simp only [d359220, d361424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37614 q selected
  have h6 (q : Pattern) (selected : d359221 q = 0) : d361425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359221, d361425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359221, d361425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359222 q = 0) : d361426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359222, d361426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359222, d361426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359258 q = 0) : d361462 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359258, d361462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37650 q selected
    | true =>
      simp only [d359258, d361462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37619 q selected
  have h9 (q : Pattern) (selected : d359286 q = 0) : d361329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359286, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37655 q selected
    | true =>
      simp only [d359286, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37624 q selected
  have h10 (q : Pattern) (selected : d359287 q = 0) : d361463 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359287, d361463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359287, d361463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359292 q = 0) : d361468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359292, d361468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37656 q selected
    | true =>
      simp only [d359292, d361468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359293 q = 0) : d361469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359293, d361469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359293, d361469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359294 q = 0) : d361470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359294, d361470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359294, d361470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359295 q = 0) : d361471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359295, d361471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359295, d361471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359296 q = 0) : d361472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359296, d361472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359296, d361472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359297 q = 0) : d361473 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359297, d361473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359297, d361473, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro37658 (p : Pattern) (selected : d359298 p = 0) : d361474 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359072 q = 0) : d361325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359073 q = 0) : d361326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359073, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359073, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359211 q = 0) : d361415 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359211, d361415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359211, d361415, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359298 q = 0) : d361474 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359298, d361474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359298, d361474, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37659 (p : Pattern) (selected : d359303 p = 0) : d361479 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d358959 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37600 q selected
    | true =>
      simp only [d358959, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358960 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358960, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359072 q = 0) : d361325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359072, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359217 q = 0) : d361421 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359217, d361421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359217, d361421, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359218 q = 0) : d361422 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359218, d361422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359218, d361422, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359303 q = 0) : d361479 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359303, d361479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359303, d361479, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37660 (p : Pattern) (selected : d359307 p = 0) : d361483 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359252 q = 0) : d361456 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359252, d361456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37649 q selected
    | true =>
      simp only [d359252, d361456, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359253 q = 0) : d361457 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359253, d361457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359253, d361457, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359254 q = 0) : d361458 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359254, d361458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359254, d361458, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359255 q = 0) : d361459 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359255, d361459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359255, d361459, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359256 q = 0) : d361460 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359256, d361460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359256, d361460, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359307 q = 0) : d361483 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359307, d361483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359307, d361483, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37661 (p : Pattern) (selected : d359309 p = 0) : d361344 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359280 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359280, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37654 q selected
    | true =>
      simp only [d359280, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359281 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359281, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359281, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359098 q = 0) : d361212 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359098, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37623 q selected
    | true =>
      simp only [d359098, d361212, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359099 q = 0) : d361213 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359099, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359099, d361213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359282 q = 0) : d361325 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359282, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359282, d361325, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359283 q = 0) : d361326 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359283, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359283, d361326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359284 q = 0) : d361327 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359284, d361327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359284, d361327, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359309 q = 0) : d361344 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359309, d361344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359309, d361344, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37662 (p : Pattern) (selected : d359312 p = 0) : d361486 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359070 q = 0) : d361323 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37618 q selected
    | true =>
      simp only [d359070, d361323, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359071 q = 0) : d361324 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359071, d361324, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359288 q = 0) : d361464 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359288, d361464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359288, d361464, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359289 q = 0) : d361465 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359289, d361465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359289, d361465, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359290 q = 0) : d361466 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359290, d361466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359290, d361466, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359312 q = 0) : d361486 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359312, d361486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359312, d361486, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37663 (p : Pattern) (selected : d359318 p = 0) : d361492 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359213 q = 0) : d361417 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359213, d361417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37643 q selected
    | true =>
      simp only [d359213, d361417, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37613 q selected
  have h2 (q : Pattern) (selected : d359214 q = 0) : d361418 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359214, d361418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359214, d361418, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359215 q = 0) : d361419 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359215, d361419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359215, d361419, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359216 q = 0) : d361420 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359216, d361420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359216, d361420, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359220 q = 0) : d361424 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359220, d361424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37644 q selected
    | true =>
      simp only [d359220, d361424, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37614 q selected
  have h6 (q : Pattern) (selected : d359221 q = 0) : d361425 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359221, d361425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359221, d361425, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359222 q = 0) : d361426 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359222, d361426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359222, d361426, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359258 q = 0) : d361462 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359258, d361462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37650 q selected
    | true =>
      simp only [d359258, d361462, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37619 q selected
  have h9 (q : Pattern) (selected : d359286 q = 0) : d361329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359286, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37655 q selected
    | true =>
      simp only [d359286, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37624 q selected
  have h10 (q : Pattern) (selected : d359287 q = 0) : d361463 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359287, d361463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359287, d361463, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359292 q = 0) : d361468 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359292, d361468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37656 q selected
    | true =>
      simp only [d359292, d361468, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359293 q = 0) : d361469 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359293, d361469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359293, d361469, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359294 q = 0) : d361470 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359294, d361470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359294, d361470, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359295 q = 0) : d361471 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359295, d361471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359295, d361471, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359296 q = 0) : d361472 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359296, d361472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359296, d361472, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359299 q = 0) : d361475 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359299, d361475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37658 q selected
    | true =>
      simp only [d359299, d361475, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37626 q selected
  have h17 (q : Pattern) (selected : d359300 q = 0) : d361476 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359300, d361476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359300, d361476, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359301 q = 0) : d361477 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359301, d361477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359301, d361477, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d359302 q = 0) : d361478 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359302, d361478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359302, d361478, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d359304 q = 0) : d361480 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359304, d361480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37659 q selected
    | true =>
      simp only [d359304, d361480, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37627 q selected
  have h21 (q : Pattern) (selected : d359305 q = 0) : d361481 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359305, d361481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359305, d361481, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d359306 q = 0) : d361482 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359306, d361482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359306, d361482, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d359308 q = 0) : d361484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359308, d361484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37660 q selected
    | true =>
      simp only [d359308, d361484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37628 q selected
  have h24 (q : Pattern) (selected : d359310 q = 0) : d361345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359310, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37661 q selected
    | true =>
      simp only [d359310, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37629 q selected
  have h25 (q : Pattern) (selected : d359311 q = 0) : d361485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359311, d361485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d359311, d361485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d359313 q = 0) : d361487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359313, d361487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37662 q selected
    | true =>
      simp only [d359313, d361487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d359314 q = 0) : d361488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359314, d361488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d359314, d361488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d359315 q = 0) : d361489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359315, d361489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d359315, d361489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d359316 q = 0) : d361490 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359316, d361490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d359316, d361490, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d359317 q = 0) : d361491 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359317, d361491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359317, d361491, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d359318 q = 0) : d361492 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359318, d361492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359318, d361492, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro37664 (p : Pattern) (selected : d359320 p = 0) : d361494 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359076 q = 0) : d361329 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37619 q selected
    | true =>
      simp only [d359076, d361329, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
  have h2 (q : Pattern) (selected : d359196 q = 0) : d361400 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359196, d361400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359196, d361400, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359197 q = 0) : d361401 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359197, d361401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359197, d361401, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359198 q = 0) : d361402 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359198, d361402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359198, d361402, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359199 q = 0) : d361403 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359199, d361403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359199, d361403, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358965 q = 0) : d361218 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37601 q selected
    | true =>
      simp only [d358965, d361218, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359022 q = 0) : d361275 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359022, d361275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359022, d361275, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359023 q = 0) : d361276 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359023, d361276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359023, d361276, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359024 q = 0) : d361277 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359024, d361277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359024, d361277, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359025 q = 0) : d361278 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359025, d361278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359025, d361278, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359320 q = 0) : d361494 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359320, d361494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359320, d361494, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37665 (p : Pattern) (selected : d359327 p = 0) : d361501 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359308 q = 0) : d361484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359308, d361484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37660 q selected
    | true =>
      simp only [d359308, d361484, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37628 q selected
  have h2 (q : Pattern) (selected : d359310 q = 0) : d361345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359310, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37661 q selected
    | true =>
      simp only [d359310, d361345, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37629 q selected
  have h3 (q : Pattern) (selected : d359311 q = 0) : d361485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359311, d361485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359311, d361485, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359313 q = 0) : d361487 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359313, d361487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37662 q selected
    | true =>
      simp only [d359313, d361487, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359314 q = 0) : d361488 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359314, d361488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359314, d361488, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359315 q = 0) : d361489 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359315, d361489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359315, d361489, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359325 q = 0) : d361499 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359325, d361499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359325, d361499, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359326 q = 0) : d361500 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359326, d361500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359326, d361500, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359327 q = 0) : d361501 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359327, d361501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359327, d361501, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37666 (p : Pattern) (selected : d359329 p = 0) : d361503 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d358972 q = 0) : d361225 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37603 q selected
    | true =>
      simp only [d358972, d361225, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359029 q = 0) : d361282 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359029, d361282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359029, d361282, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359030 q = 0) : d361283 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359030, d361283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359030, d361283, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359031 q = 0) : d361284 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359031, d361284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359031, d361284, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359032 q = 0) : d361285 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359032, d361285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359032, d361285, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359329 q = 0) : d361503 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359329, d361503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359329, d361503, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37667 (p : Pattern) (selected : d359345 p = 0) : d361519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359335 q = 0) : d361509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359335, d361509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359335, d361509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37646 q selected
  have h2 (q : Pattern) (selected : d359232 q = 0) : d361436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359232, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37646 q selected
    | true =>
      simp only [d359232, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359336 q = 0) : d361510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359336, d361510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359336, d361510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359233 q = 0) : d361437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359233, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359233, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359337 q = 0) : d361511 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359337, d361511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359337, d361511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359338 q = 0) : d361512 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359338, d361512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359338, d361512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359142 q = 0) : d361365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359142, d361365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359142, d361365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37616 q selected
  have h8 (q : Pattern) (selected : d359058 q = 0) : d361311 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359058, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37616 q selected
    | true =>
      simp only [d359058, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359143 q = 0) : d361366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359143, d361366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359143, d361366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359059 q = 0) : d361312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359059, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359059, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359144 q = 0) : d361367 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359144, d361367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359144, d361367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359145 q = 0) : d361368 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359145, d361368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359145, d361368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359339 q = 0) : d361513 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359339, d361513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359339, d361513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359340 q = 0) : d361514 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359340, d361514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359340, d361514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
  have h15 (q : Pattern) (selected : d359240 q = 0) : d361444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
    | true =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359341 q = 0) : d361515 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359341, d361515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359341, d361515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359241 q = 0) : d361445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359342 q = 0) : d361516 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359342, d361516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359342, d361516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359343 q = 0) : d361517 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359343, d361517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d359343, d361517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d358988 q = 0) : d361241 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358988, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358988, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
  have h21 (q : Pattern) (selected : d358947 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
    | true =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d358989 q = 0) : d361242 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358989, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d358989, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d358948 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d358990 q = 0) : d361243 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d358990, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d358990, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d358991 q = 0) : d361244 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d358991, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d358991, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d359344 q = 0) : d361518 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359344, d361518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359344, d361518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d359345 q = 0) : d361519 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359345, d361519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359345, d361519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro37668 (p : Pattern) (selected : d359351 p = 0) : d361525 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359346 q = 0) : d361520 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359346, d361520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37667 q selected
    | true =>
      simp only [d359346, d361520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37633 q selected
  have h2 (q : Pattern) (selected : d359347 q = 0) : d361521 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359347, d361521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359347, d361521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359348 q = 0) : d361522 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359348, d361522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359348, d361522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359148 q = 0) : d361371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37633 q selected
    | true =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37606 q selected
  have h5 (q : Pattern) (selected : d359149 q = 0) : d361372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359150 q = 0) : d361373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359349 q = 0) : d361523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359349, d361523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359349, d361523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d358994 q = 0) : d361247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d358994, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37606 q selected
    | true =>
      simp only [d358994, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358995 q = 0) : d361248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d358995, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358995, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d358996 q = 0) : d361249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d358996, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358996, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359151 q = 0) : d361374 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359151, d361374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359151, d361374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359350 q = 0) : d361524 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359350, d361524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359350, d361524, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359351 q = 0) : d361525 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359351, d361525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359351, d361525, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h13 p selected
theorem eqIntro37669 (p : Pattern) (selected : d359357 p = 0) : d361531 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359352 q = 0) : d361526 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359352, d361526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37668 q selected
    | true =>
      simp only [d359352, d361526, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359353 q = 0) : d361527 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359353, d361527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359353, d361527, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359154 q = 0) : d361377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359154, d361377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37634 q selected
    | true =>
      simp only [d359154, d361377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359155 q = 0) : d361378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359155, d361378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359155, d361378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359354 q = 0) : d361528 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359354, d361528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359354, d361528, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359355 q = 0) : d361529 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359355, d361529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359355, d361529, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359356 q = 0) : d361530 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359356, d361530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359356, d361530, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359357 q = 0) : d361531 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359357, d361531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359357, d361531, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37670 (p : Pattern) (selected : d359364 p = 0) : d361370 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359359 q = 0) : d361365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359359, d361365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359359, d361365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37652 q selected
  have h2 (q : Pattern) (selected : d359268 q = 0) : d361311 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359268, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37652 q selected
    | true =>
      simp only [d359268, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359360 q = 0) : d361366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359360, d361366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359360, d361366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359269 q = 0) : d361312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359269, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359269, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359361 q = 0) : d361367 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359361, d361367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359361, d361367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359362 q = 0) : d361368 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359362, d361368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359362, d361368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359161 q = 0) : d361241 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359161, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359161, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
  have h8 (q : Pattern) (selected : d359086 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
    | true =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359162 q = 0) : d361242 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359162, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359162, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359087 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359163 q = 0) : d361243 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359163, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359163, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359164 q = 0) : d361244 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359164, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359164, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359363 q = 0) : d361369 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359363, d361369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359363, d361369, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359165 q = 0) : d361245 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359165, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359165, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359364 q = 0) : d361370 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359364, d361370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359364, d361370, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37671 (p : Pattern) (selected : d359370 p = 0) : d361376 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359365 q = 0) : d361371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359365, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37670 q selected
    | true =>
      simp only [d359365, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37636 q selected
  have h2 (q : Pattern) (selected : d359366 q = 0) : d361372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359366, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359366, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359367 q = 0) : d361373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359367, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359367, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359167 q = 0) : d361247 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359167, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37636 q selected
    | true =>
      simp only [d359167, d361247, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359168 q = 0) : d361248 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359168, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359168, d361248, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359169 q = 0) : d361249 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359169, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359169, d361249, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359368 q = 0) : d361374 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359368, d361374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359368, d361374, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359170 q = 0) : d361250 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359170, d361250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359170, d361250, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359369 q = 0) : d361375 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359369, d361375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359369, d361375, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359370 q = 0) : d361376 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359370, d361376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359370, d361376, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37672 (p : Pattern) (selected : d359376 p = 0) : d361382 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359371 q = 0) : d361377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359371, d361377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37671 q selected
    | true =>
      simp only [d359371, d361377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359372 q = 0) : d361378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359372, d361378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359372, d361378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359173 q = 0) : d361253 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359173, d361253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37637 q selected
    | true =>
      simp only [d359173, d361253, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359174 q = 0) : d361254 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359174, d361254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359174, d361254, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359373 q = 0) : d361379 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359373, d361379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359373, d361379, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359374 q = 0) : d361380 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359374, d361380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359374, d361380, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359375 q = 0) : d361381 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359375, d361381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359375, d361381, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359376 q = 0) : d361382 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359376, d361382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359376, d361382, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37673 (p : Pattern) (selected : d359382 p = 0) : d361537 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359154 q = 0) : d361377 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359154, d361377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37634 q selected
    | true =>
      simp only [d359154, d361377, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359155 q = 0) : d361378 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359155, d361378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359155, d361378, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359379 q = 0) : d361534 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359379, d361534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359379, d361534, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359380 q = 0) : d361535 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359380, d361535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359380, d361535, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359381 q = 0) : d361536 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359381, d361536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359381, d361536, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359382 q = 0) : d361537 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359382, d361537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359382, d361537, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37674 (p : Pattern) (selected : d359388 p = 0) : d361543 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359358 q = 0) : d361532 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359358, d361532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37669 q selected
    | true =>
      simp only [d359358, d361532, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37635 q selected
  have h2 (q : Pattern) (selected : d359377 q = 0) : d361383 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359377, d361383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37672 q selected
    | true =>
      simp only [d359377, d361383, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37638 q selected
  have h3 (q : Pattern) (selected : d359378 q = 0) : d361533 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359378, d361533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359378, d361533, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359383 q = 0) : d361538 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359383, d361538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37673 q selected
    | true =>
      simp only [d359383, d361538, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359384 q = 0) : d361539 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359384, d361539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359384, d361539, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359385 q = 0) : d361540 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359385, d361540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359385, d361540, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359386 q = 0) : d361541 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359386, d361541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359386, d361541, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359387 q = 0) : d361542 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359387, d361542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359387, d361542, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359388 q = 0) : d361543 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359388, d361543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359388, d361543, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37675 (p : Pattern) (selected : d359394 p = 0) : d361549 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359006 q = 0) : d361259 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359006, d361259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37608 q selected
    | true =>
      simp only [d359006, d361259, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359390 q = 0) : d361545 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359390, d361545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359390, d361545, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359391 q = 0) : d361546 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359391, d361546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359391, d361546, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359392 q = 0) : d361547 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359392, d361547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359392, d361547, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359393 q = 0) : d361548 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359393, d361548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359393, d361548, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359394 q = 0) : d361549 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359394, d361549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359394, d361549, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37676 (p : Pattern) (selected : d359400 p = 0) : d361555 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359201 q = 0) : d361405 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359201, d361405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359201, d361405, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37641 q selected
  have h2 (q : Pattern) (selected : d359202 q = 0) : d361406 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359202, d361406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359202, d361406, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359208 q = 0) : d361412 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359208, d361412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37641 q selected
    | true =>
      simp only [d359208, d361412, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37642 q selected
  have h4 (q : Pattern) (selected : d359209 q = 0) : d361413 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359209, d361413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359209, d361413, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359210 q = 0) : d361414 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359210, d361414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359210, d361414, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359319 q = 0) : d361493 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359319, d361493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37657 q selected
    | true =>
      simp only [d359319, d361493, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37663 q selected
  have h7 (q : Pattern) (selected : d359321 q = 0) : d361495 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359321, d361495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37664 q selected
    | true =>
      simp only [d359321, d361495, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37612 q selected
  have h8 (q : Pattern) (selected : d359322 q = 0) : d361496 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359322, d361496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359322, d361496, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359323 q = 0) : d361497 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359323, d361497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359323, d361497, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359324 q = 0) : d361498 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359324, d361498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359324, d361498, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359328 q = 0) : d361502 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359328, d361502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359328, d361502, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37665 q selected
  have h12 (q : Pattern) (selected : d359330 q = 0) : d361504 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359330, d361504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359330, d361504, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37666 q selected
  have h13 (q : Pattern) (selected : d359331 q = 0) : d361505 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359331, d361505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359331, d361505, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359332 q = 0) : d361506 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359332, d361506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359332, d361506, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359333 q = 0) : d361507 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359333, d361507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359333, d361507, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359334 q = 0) : d361508 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359334, d361508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359334, d361508, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359389 q = 0) : d361544 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359389, d361544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359389, d361544, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37674 q selected
  have h18 (q : Pattern) (selected : d359395 q = 0) : d361550 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359395, d361550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359395, d361550, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37675 q selected
  have h19 (q : Pattern) (selected : d359396 q = 0) : d361551 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359396, d361551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359396, d361551, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d359397 q = 0) : d361552 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359397, d361552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359397, d361552, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d359398 q = 0) : d361553 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359398, d361553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d359398, d361553, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d359399 q = 0) : d361554 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359399, d361554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359399, d361554, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d359400 q = 0) : d361555 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d359400, d361555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359400, d361555, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro37677 (p : Pattern) (selected : d359406 p = 0) : d361561 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359018 q = 0) : d361271 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359018, d361271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359018, d361271, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37610 q selected
  have h2 (q : Pattern) (selected : d359019 q = 0) : d361272 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359019, d361272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359019, d361272, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359020 q = 0) : d361273 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359020, d361273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359020, d361273, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359021 q = 0) : d361274 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359021, d361274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359021, d361274, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359191 q = 0) : d361395 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359191, d361395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359191, d361395, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37640 q selected
  have h6 (q : Pattern) (selected : d359192 q = 0) : d361396 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359192, d361396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359192, d361396, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359193 q = 0) : d361397 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359193, d361397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359193, d361397, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359194 q = 0) : d361398 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359194, d361398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359194, d361398, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359195 q = 0) : d361399 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d359195, d361399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359195, d361399, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359401 q = 0) : d361556 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359401, d361556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359401, d361556, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37676 q selected
  have h11 (q : Pattern) (selected : d359402 q = 0) : d361557 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359402, d361557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359402, d361557, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359403 q = 0) : d361558 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359403, d361558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359403, d361558, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359404 q = 0) : d361559 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359404, d361559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359404, d361559, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359405 q = 0) : d361560 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d359405, d361560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359405, d361560, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359406 q = 0) : d361561 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d359406, d361561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359406, d361561, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37678 (p : Pattern) (selected : d359409 p = 0) : d361564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359246 q = 0) : d361450 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359246, d361450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37648 q selected
    | true =>
      simp only [d359246, d361450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37617 q selected
  have h2 (q : Pattern) (selected : d359247 q = 0) : d361451 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359247, d361451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359247, d361451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359248 q = 0) : d361452 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359248, d361452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359248, d361452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359064 q = 0) : d361317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37617 q selected
    | true =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37599 q selected
  have h5 (q : Pattern) (selected : d359065 q = 0) : d361318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359066 q = 0) : d361319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359249 q = 0) : d361453 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359249, d361453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359249, d361453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359407 q = 0) : d361562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359407, d361562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359407, d361562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359408 q = 0) : d361563 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359408, d361563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359408, d361563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359409 q = 0) : d361564 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359409, d361564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359409, d361564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37679 (p : Pattern) (selected : d359413 p = 0) : d361568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359064 q = 0) : d361317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37617 q selected
    | true =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37599 q selected
  have h2 (q : Pattern) (selected : d359065 q = 0) : d361318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359066 q = 0) : d361319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359407 q = 0) : d361562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359407, d361562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359407, d361562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359412 q = 0) : d361567 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359412, d361567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359412, d361567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359413 q = 0) : d361568 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359413, d361568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359413, d361568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37680 (p : Pattern) (selected : d359419 p = 0) : d361574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359416 q = 0) : d361571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359417 q = 0) : d361572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359417, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359417, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359418 q = 0) : d361573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359418, d361573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359418, d361573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359419 q = 0) : d361574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359419, d361574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359419, d361574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37681 (p : Pattern) (selected : d359423 p = 0) : d361578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359420 q = 0) : d361575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359421 q = 0) : d361576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359421, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359421, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359422 q = 0) : d361577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359422, d361577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359422, d361577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359423 q = 0) : d361578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359423, d361578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359423, d361578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37682 (p : Pattern) (selected : d359429 p = 0) : d361584 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359424 q = 0) : d361579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359424, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37680 q selected
    | true =>
      simp only [d359424, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37681 q selected
  have h2 (q : Pattern) (selected : d359425 q = 0) : d361580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359425, d361580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359425, d361580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359426 q = 0) : d361581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359426, d361581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359426, d361581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359427 q = 0) : d361582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359427, d361582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359427, d361582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359428 q = 0) : d361583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359428, d361583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359428, d361583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359429 q = 0) : d361584 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359429, d361584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359429, d361584, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37683 (p : Pattern) (selected : d359432 p = 0) : d361587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359416 q = 0) : d361571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359417 q = 0) : d361572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359417, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359417, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359418 q = 0) : d361573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359418, d361573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359418, d361573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359432 q = 0) : d361587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359432, d361587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359432, d361587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37684 (p : Pattern) (selected : d359433 p = 0) : d361588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359420 q = 0) : d361575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359421 q = 0) : d361576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359421, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359421, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359422 q = 0) : d361577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359422, d361577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359422, d361577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359433 q = 0) : d361588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359433, d361588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359433, d361588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37685 (p : Pattern) (selected : d359439 p = 0) : d361594 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359424 q = 0) : d361579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359424, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37680 q selected
    | true =>
      simp only [d359424, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37681 q selected
  have h2 (q : Pattern) (selected : d359425 q = 0) : d361580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359425, d361580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359425, d361580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359426 q = 0) : d361581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359426, d361581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359426, d361581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359427 q = 0) : d361582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359427, d361582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359427, d361582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359428 q = 0) : d361583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359428, d361583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359428, d361583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359434 q = 0) : d361589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359434, d361589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37683 q selected
    | true =>
      simp only [d359434, d361589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37684 q selected
  have h7 (q : Pattern) (selected : d359435 q = 0) : d361590 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359435, d361590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359435, d361590, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359436 q = 0) : d361591 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359436, d361591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359436, d361591, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359437 q = 0) : d361592 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359437, d361592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359437, d361592, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359438 q = 0) : d361593 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359438, d361593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359438, d361593, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359439 q = 0) : d361594 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359439, d361594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359439, d361594, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37686 (p : Pattern) (selected : d359444 p = 0) : d361599 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359416 q = 0) : d361571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359417 q = 0) : d361572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359417, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359417, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359443 q = 0) : d361598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359443, d361598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359443, d361598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359444 q = 0) : d361599 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359444, d361599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359444, d361599, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37687 (p : Pattern) (selected : d359446 p = 0) : d361601 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359420 q = 0) : d361575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359421 q = 0) : d361576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359421, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359421, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359445 q = 0) : d361600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359445, d361600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359445, d361600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359446 q = 0) : d361601 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359446, d361601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359446, d361601, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37688 (p : Pattern) (selected : d359453 p = 0) : d361608 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359416 q = 0) : d361571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359451 q = 0) : d361606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359451, d361606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359451, d361606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359452 q = 0) : d361607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359452, d361607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359452, d361607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359453 q = 0) : d361608 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359453, d361608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359453, d361608, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37689 (p : Pattern) (selected : d359456 p = 0) : d361611 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359420 q = 0) : d361575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359454 q = 0) : d361609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359454, d361609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359454, d361609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359455 q = 0) : d361610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359455, d361610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359455, d361610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359456 q = 0) : d361611 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359456, d361611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359456, d361611, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37690 (p : Pattern) (selected : d359461 p = 0) : d361616 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d271326 q = 0) : d271213 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271326, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d271326, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d271213 q = 0) : d271326 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d271327 q = 0) : d273807 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271327, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271327, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d271214 q = 0) : d273695 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359049 q = 0) : d361302 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359049, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359049, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359460 q = 0) : d361615 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359460, d361615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359460, d361615, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359461 q = 0) : d361616 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359461, d361616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359461, d361616, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37691 (p : Pattern) (selected : d359468 p = 0) : d361623 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d1 q = 0) : d0 q = 1 := by
    change (1 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d271213 q = 0) : d271326 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271213, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272403 q = 0) : d274587 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272403, d274587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272403, d274587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359223 q = 0) : d361427 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359223, d361427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359223, d361427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d271326 q = 0) : d271213 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271326, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d271326, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d271327 q = 0) : d273807 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271327, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d271327, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d359465 q = 0) : d361620 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359465, d361620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359465, d361620, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359466 q = 0) : d361621 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359466, d361621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359466, d361621, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d271214 q = 0) : d273695 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271214, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d358938 q = 0) : d361191 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d358938, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d358938, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359467 q = 0) : d361622 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359467, d361622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359467, d361622, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359468 q = 0) : d361623 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359468, d361623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359468, d361623, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro37692 (p : Pattern) (selected : d359474 p = 0) : d361629 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359462 q = 0) : d361617 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359462, d361617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37690 q selected
    | true =>
      simp only [d359462, d361617, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359463 q = 0) : d361618 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359463, d361618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359463, d361618, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359226 q = 0) : d361430 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359226, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37645 q selected
    | true =>
      simp only [d359226, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359227 q = 0) : d361431 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359227, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359227, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359464 q = 0) : d361619 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359464, d361619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359464, d361619, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359469 q = 0) : d361624 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359469, d361624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37691 q selected
    | true =>
      simp only [d359469, d361624, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359470 q = 0) : d361625 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359470, d361625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359470, d361625, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359052 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37615 q selected
    | true =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359053 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359471 q = 0) : d361626 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359471, d361626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359471, d361626, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359472 q = 0) : d361627 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359472, d361627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359472, d361627, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359473 q = 0) : d361628 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359473, d361628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359473, d361628, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359228 q = 0) : d361432 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359228, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359228, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h14 (q : Pattern) (selected : d358941 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37597 q selected
    | true =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d358942 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359054 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359229 q = 0) : d361433 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359229, d361433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359229, d361433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359230 q = 0) : d361434 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359230, d361434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359230, d361434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d359474 q = 0) : d361629 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359474, d361629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359474, d361629, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro37693 (p : Pattern) (selected : d359479 p = 0) : d361634 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359226 q = 0) : d361430 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359226, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37645 q selected
    | true =>
      simp only [d359226, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359227 q = 0) : d361431 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359227, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359227, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359052 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37615 q selected
    | true =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359053 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359228 q = 0) : d361432 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359228, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359228, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358941 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37597 q selected
    | true =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358942 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359054 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359229 q = 0) : d361433 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359229, d361433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359229, d361433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359230 q = 0) : d361434 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359230, d361434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359230, d361434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359237 q = 0) : d361441 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359237, d361441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359237, d361441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359238 q = 0) : d361442 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359238, d361442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359238, d361442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359479 q = 0) : d361634 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359479, d361634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359479, d361634, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro37694 (p : Pattern) (selected : d359487 p = 0) : d361642 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359226 q = 0) : d361430 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359226, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37645 q selected
    | true =>
      simp only [d359226, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359227 q = 0) : d361431 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359227, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359227, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359052 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37615 q selected
    | true =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359053 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359228 q = 0) : d361432 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359228, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359228, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359485 q = 0) : d361640 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359485, d361640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359485, d361640, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359486 q = 0) : d361641 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359486, d361641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359486, d361641, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d358941 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37597 q selected
    | true =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358942 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359054 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359237 q = 0) : d361441 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359237, d361441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359237, d361441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359238 q = 0) : d361442 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359238, d361442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359238, d361442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359487 q = 0) : d361642 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359487, d361642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359487, d361642, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  exact h13 p selected
theorem eqIntro37695 (p : Pattern) (selected : d359493 p = 0) : d361648 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359475 q = 0) : d361630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359475, d361630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37692 q selected
    | true =>
      simp only [d359475, d361630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359476 q = 0) : d361631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359476, d361631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359476, d361631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359477 q = 0) : d361632 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359477, d361632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359477, d361632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359478 q = 0) : d361633 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359478, d361633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359478, d361633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359480 q = 0) : d361635 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359480, d361635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37693 q selected
    | true =>
      simp only [d359480, d361635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359481 q = 0) : d361636 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359481, d361636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359481, d361636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359482 q = 0) : d361637 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359482, d361637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359482, d361637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359483 q = 0) : d361638 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359483, d361638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359483, d361638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359484 q = 0) : d361639 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359484, d361639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359484, d361639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359488 q = 0) : d361643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359488, d361643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37694 q selected
    | true =>
      simp only [d359488, d361643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359489 q = 0) : d361644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359489, d361644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359489, d361644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359490 q = 0) : d361645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359490, d361645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359490, d361645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359491 q = 0) : d361646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359491, d361646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359491, d361646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359240 q = 0) : d361444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
    | true =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359241 q = 0) : d361445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359242 q = 0) : d361446 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359242, d361446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359242, d361446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359243 q = 0) : d361447 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359243, d361447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359243, d361447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359492 q = 0) : d361647 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359492, d361647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359492, d361647, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359493 q = 0) : d361648 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359493, d361648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359493, d361648, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro37696 (p : Pattern) (selected : d359497 p = 0) : d361652 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359240 q = 0) : d361444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
    | true =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359241 q = 0) : d361445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359242 q = 0) : d361446 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359242, d361446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359242, d361446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359243 q = 0) : d361447 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359243, d361447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359243, d361447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d358947 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
    | true =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d358948 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358949 q = 0) : d361202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d358949, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358949, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d358950 q = 0) : d361203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d358950, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358950, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359244 q = 0) : d361448 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359244, d361448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359244, d361448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d358951 q = 0) : d361204 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d358951, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d358951, d361204, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359497 q = 0) : d361652 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359497, d361652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359497, d361652, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37697 (p : Pattern) (selected : d359503 p = 0) : d361658 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359494 q = 0) : d361649 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359494, d361649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37695 q selected
    | true =>
      simp only [d359494, d361649, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37648 q selected
  have h2 (q : Pattern) (selected : d359495 q = 0) : d361650 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359495, d361650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359495, d361650, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359496 q = 0) : d361651 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359496, d361651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359496, d361651, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359498 q = 0) : d361653 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359498, d361653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37648 q selected
    | true =>
      simp only [d359498, d361653, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37696 q selected
  have h5 (q : Pattern) (selected : d359499 q = 0) : d361654 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359499, d361654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359499, d361654, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359500 q = 0) : d361655 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359500, d361655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359500, d361655, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359501 q = 0) : d361656 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359501, d361656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359501, d361656, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359246 q = 0) : d361450 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359246, d361450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37648 q selected
    | true =>
      simp only [d359246, d361450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37617 q selected
  have h9 (q : Pattern) (selected : d359247 q = 0) : d361451 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359247, d361451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359247, d361451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359248 q = 0) : d361452 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359248, d361452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359248, d361452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359064 q = 0) : d361317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37617 q selected
    | true =>
      simp only [d359064, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37599 q selected
  have h12 (q : Pattern) (selected : d359065 q = 0) : d361318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359065, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359066 q = 0) : d361319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359066, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359249 q = 0) : d361453 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359249, d361453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359249, d361453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359502 q = 0) : d361657 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359502, d361657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359502, d361657, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359503 q = 0) : d361658 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359503, d361658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359503, d361658, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro37698 (p : Pattern) (selected : d359509 p = 0) : d361664 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359504 q = 0) : d361659 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359504, d361659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37697 q selected
    | true =>
      simp only [d359504, d361659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359505 q = 0) : d361660 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359505, d361660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359505, d361660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359506 q = 0) : d361661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359506, d361661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359506, d361661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359507 q = 0) : d361662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359507, d361662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359507, d361662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359508 q = 0) : d361663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359508, d361663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359508, d361663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359509 q = 0) : d361664 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359509, d361664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359509, d361664, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37699 (p : Pattern) (selected : d359513 p = 0) : d361429 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d2 q = 0) : d0 q = 1 := by
    change (2 : Int) = 0 at selected
    omega
  have h2 (q : Pattern) (selected : d271355 q = 0) : d271326 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d271355, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d271355, d271326, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d272612 q = 0) : d274587 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d272612, d274587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d272612, d274587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359511 q = 0) : d361427 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359511, d361427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359511, d361427, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d49282 q = 0) : d271213 q = 1 := by
    cases bit : q 247 with
    | false =>
      simp only [d49282, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d49282, d271213, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h6 (q : Pattern) (selected : d271538 q = 0) : d273807 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271538, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d271538, d273807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h7 (q : Pattern) (selected : d271356 q = 0) : d273695 q = 1 := by
    cases bit : q 246 with
    | false =>
      simp only [d271356, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d271356, d273695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359259 q = 0) : d361302 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359259, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359259, d361302, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359512 q = 0) : d361428 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359512, d361428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359512, d361428, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359077 q = 0) : d361191 q = 1 := by
    cases bit : q 226 with
    | false =>
      simp only [d359077, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359077, d361191, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359260 q = 0) : d361303 q = 1 := by
    cases bit : q 225 with
    | false =>
      simp only [d359260, d361303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359260, d361303, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359513 q = 0) : d361429 q = 1 := by
    cases bit : q 224 with
    | false =>
      simp only [d359513, d361429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359513, d361429, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  exact h12 p selected
theorem eqIntro37700 (p : Pattern) (selected : d359519 p = 0) : d361435 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359514 q = 0) : d361430 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359514, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37699 q selected
    | true =>
      simp only [d359514, d361430, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359515 q = 0) : d361431 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359515, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359515, d361431, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359262 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37651 q selected
    | true =>
      simp only [d359262, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359263 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359263, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359516 q = 0) : d361432 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359516, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359516, d361432, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359080 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37620 q selected
    | true =>
      simp only [d359080, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359081 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359081, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359264 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359264, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359517 q = 0) : d361433 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359517, d361433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359517, d361433, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359518 q = 0) : d361434 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359518, d361434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359518, d361434, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359082 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359082, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359265 q = 0) : d361308 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359265, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359265, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359266 q = 0) : d361309 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359266, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359266, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359519 q = 0) : d361435 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359519, d361435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359519, d361435, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  exact h14 p selected
theorem eqIntro37701 (p : Pattern) (selected : d359527 p = 0) : d361443 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359262 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359262, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37651 q selected
    | true =>
      simp only [d359262, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359263 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359263, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359263, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359080 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359080, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37620 q selected
    | true =>
      simp only [d359080, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359081 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359081, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359081, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359264 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359264, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359264, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359525 q = 0) : d361441 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359525, d361441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359525, d361441, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359526 q = 0) : d361442 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359526, d361442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359526, d361442, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359082 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359082, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359082, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359083 q = 0) : d361197 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359083, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359083, d361197, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359084 q = 0) : d361198 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359084, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359084, d361198, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359527 q = 0) : d361443 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359527, d361443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359527, d361443, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37702 (p : Pattern) (selected : d359533 p = 0) : d361449 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359520 q = 0) : d361436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359520, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37700 q selected
    | true =>
      simp only [d359520, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359521 q = 0) : d361437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359521, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359521, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359522 q = 0) : d361438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359522, d361438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359522, d361438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359523 q = 0) : d361439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359523, d361439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359523, d361439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359268 q = 0) : d361311 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359268, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37652 q selected
    | true =>
      simp only [d359268, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359269 q = 0) : d361312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359269, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359269, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359270 q = 0) : d361313 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359270, d361313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359270, d361313, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359271 q = 0) : d361314 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359271, d361314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359271, d361314, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359524 q = 0) : d361440 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359524, d361440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359524, d361440, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359528 q = 0) : d361444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359528, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37701 q selected
    | true =>
      simp only [d359528, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359529 q = 0) : d361445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359529, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359529, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359530 q = 0) : d361446 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359530, d361446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359530, d361446, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359531 q = 0) : d361447 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359531, d361447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359531, d361447, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359086 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
    | true =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359087 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359088 q = 0) : d361202 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359088, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359088, d361202, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359089 q = 0) : d361203 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359089, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359089, d361203, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359532 q = 0) : d361448 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359532, d361448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359532, d361448, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359533 q = 0) : d361449 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359533, d361449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359533, d361449, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro37703 (p : Pattern) (selected : d359540 p = 0) : d361564 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359534 q = 0) : d361450 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359534, d361450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37702 q selected
    | true =>
      simp only [d359534, d361450, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37653 q selected
  have h2 (q : Pattern) (selected : d359535 q = 0) : d361451 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359535, d361451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359535, d361451, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359536 q = 0) : d361452 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359536, d361452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359536, d361452, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359274 q = 0) : d361317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359274, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37653 q selected
    | true =>
      simp only [d359274, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37622 q selected
  have h5 (q : Pattern) (selected : d359275 q = 0) : d361318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359275, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359275, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359276 q = 0) : d361319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359276, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359276, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359537 q = 0) : d361453 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359537, d361453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359537, d361453, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359538 q = 0) : d361562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359538, d361562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359538, d361562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359539 q = 0) : d361563 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359539, d361563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359539, d361563, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359540 q = 0) : d361564 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359540, d361564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359540, d361564, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37704 (p : Pattern) (selected : d359544 p = 0) : d361568 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359274 q = 0) : d361317 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359274, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37653 q selected
    | true =>
      simp only [d359274, d361317, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37622 q selected
  have h2 (q : Pattern) (selected : d359275 q = 0) : d361318 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359275, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359275, d361318, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359276 q = 0) : d361319 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359276, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359276, d361319, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359538 q = 0) : d361562 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359538, d361562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359538, d361562, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359543 q = 0) : d361567 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359543, d361567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359543, d361567, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359544 q = 0) : d361568 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359544, d361568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359544, d361568, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37705 (p : Pattern) (selected : d359550 p = 0) : d361574 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359541 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359541, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37703 q selected
    | true =>
      simp only [d359541, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359542 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359542, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359542, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359545 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359545, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37704 q selected
    | true =>
      simp only [d359545, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359546 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359546, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359546, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359547 q = 0) : d361571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359547, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359547, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359548 q = 0) : d361572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359548, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359548, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359549 q = 0) : d361573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359549, d361573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359549, d361573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359550 q = 0) : d361574 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359550, d361574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359550, d361574, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37706 (p : Pattern) (selected : d359554 p = 0) : d361578 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359545 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359545, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37704 q selected
    | true =>
      simp only [d359545, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359546 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359546, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359546, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359551 q = 0) : d361575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359551, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359551, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359552 q = 0) : d361576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359552, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359552, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359553 q = 0) : d361577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359553, d361577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359553, d361577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359554 q = 0) : d361578 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359554, d361578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359554, d361578, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37707 (p : Pattern) (selected : d359560 p = 0) : d361670 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359557 q = 0) : d361667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359557, d361667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359557, d361667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359558 q = 0) : d361668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359558, d361668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359558, d361668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359559 q = 0) : d361669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359559, d361669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359559, d361669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359560 q = 0) : d361670 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359560, d361670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359560, d361670, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37708 (p : Pattern) (selected : d359566 p = 0) : d361676 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359447 q = 0) : d361602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359447, d361602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37686 q selected
    | true =>
      simp only [d359447, d361602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37687 q selected
  have h2 (q : Pattern) (selected : d359448 q = 0) : d361603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359448, d361603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359448, d361603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359449 q = 0) : d361604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359449, d361604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359449, d361604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359450 q = 0) : d361605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359450, d361605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359450, d361605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359457 q = 0) : d361612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359457, d361612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37688 q selected
    | true =>
      simp only [d359457, d361612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37689 q selected
  have h6 (q : Pattern) (selected : d359458 q = 0) : d361613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359458, d361613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359458, d361613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359459 q = 0) : d361614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359459, d361614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359459, d361614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359510 q = 0) : d361665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359510, d361665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37698 q selected
    | true =>
      simp only [d359510, d361665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37680 q selected
  have h9 (q : Pattern) (selected : d359555 q = 0) : d361579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359555, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37705 q selected
    | true =>
      simp only [d359555, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37706 q selected
  have h10 (q : Pattern) (selected : d359556 q = 0) : d361666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359556, d361666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359556, d361666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359561 q = 0) : d361671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359561, d361671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37707 q selected
    | true =>
      simp only [d359561, d361671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359562 q = 0) : d361672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359562, d361672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359562, d361672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359563 q = 0) : d361673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359563, d361673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359563, d361673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359564 q = 0) : d361674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359564, d361674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359564, d361674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359565 q = 0) : d361675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359565, d361675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359565, d361675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359566 q = 0) : d361676 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359566, d361676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359566, d361676, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  exact h16 p selected
theorem eqIntro37709 (p : Pattern) (selected : d359567 p = 0) : d361677 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359416 q = 0) : d361571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359417 q = 0) : d361572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359417, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359417, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359443 q = 0) : d361598 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359443, d361598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359443, d361598, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359567 q = 0) : d361677 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359567, d361677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359567, d361677, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37710 (p : Pattern) (selected : d359568 p = 0) : d361678 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359420 q = 0) : d361575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359421 q = 0) : d361576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359421, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359421, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359445 q = 0) : d361600 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359445, d361600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359445, d361600, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359568 q = 0) : d361678 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359568, d361678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359568, d361678, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37711 (p : Pattern) (selected : d359573 p = 0) : d361683 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359416 q = 0) : d361571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359416, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359451 q = 0) : d361606 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359451, d361606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359451, d361606, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359452 q = 0) : d361607 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359452, d361607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359452, d361607, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359573 q = 0) : d361683 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359573, d361683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359573, d361683, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37712 (p : Pattern) (selected : d359574 p = 0) : d361684 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359414 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37679 q selected
    | true =>
      simp only [d359414, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359415 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359415, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359420 q = 0) : d361575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359420, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359454 q = 0) : d361609 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359454, d361609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359454, d361609, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359455 q = 0) : d361610 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359455, d361610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359455, d361610, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359574 q = 0) : d361684 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359574, d361684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359574, d361684, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37713 (p : Pattern) (selected : d359578 p = 0) : d361688 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359504 q = 0) : d361659 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359504, d361659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37697 q selected
    | true =>
      simp only [d359504, d361659, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359505 q = 0) : d361660 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359505, d361660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359505, d361660, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359506 q = 0) : d361661 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359506, d361661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359506, d361661, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359507 q = 0) : d361662 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359507, d361662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359507, d361662, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359508 q = 0) : d361663 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359508, d361663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359508, d361663, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359578 q = 0) : d361688 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359578, d361688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359578, d361688, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37714 (p : Pattern) (selected : d359580 p = 0) : d361587 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359541 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359541, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37703 q selected
    | true =>
      simp only [d359541, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359542 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359542, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359542, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359545 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359545, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37704 q selected
    | true =>
      simp only [d359545, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359546 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359546, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359546, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359547 q = 0) : d361571 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359547, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359547, d361571, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359548 q = 0) : d361572 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359548, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359548, d361572, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359549 q = 0) : d361573 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359549, d361573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359549, d361573, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359580 q = 0) : d361587 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359580, d361587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359580, d361587, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37715 (p : Pattern) (selected : d359581 p = 0) : d361588 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359545 q = 0) : d361569 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359545, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37704 q selected
    | true =>
      simp only [d359545, d361569, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359546 q = 0) : d361570 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359546, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359546, d361570, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359551 q = 0) : d361575 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359551, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359551, d361575, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359552 q = 0) : d361576 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359552, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359552, d361576, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359553 q = 0) : d361577 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359553, d361577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359553, d361577, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359581 q = 0) : d361588 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359581, d361588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359581, d361588, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37716 (p : Pattern) (selected : d359584 p = 0) : d361691 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359410 q = 0) : d361565 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37678 q selected
    | true =>
      simp only [d359410, d361565, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359411 q = 0) : d361566 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359411, d361566, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359557 q = 0) : d361667 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359557, d361667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359557, d361667, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359558 q = 0) : d361668 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359558, d361668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359558, d361668, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359559 q = 0) : d361669 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359559, d361669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359559, d361669, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359584 q = 0) : d361691 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359584, d361691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359584, d361691, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37717 (p : Pattern) (selected : d359590 p = 0) : d361697 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359447 q = 0) : d361602 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359447, d361602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37686 q selected
    | true =>
      simp only [d359447, d361602, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37687 q selected
  have h2 (q : Pattern) (selected : d359448 q = 0) : d361603 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359448, d361603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359448, d361603, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359449 q = 0) : d361604 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359449, d361604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359449, d361604, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359450 q = 0) : d361605 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359450, d361605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359450, d361605, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359457 q = 0) : d361612 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359457, d361612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37688 q selected
    | true =>
      simp only [d359457, d361612, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37689 q selected
  have h6 (q : Pattern) (selected : d359458 q = 0) : d361613 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359458, d361613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359458, d361613, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359459 q = 0) : d361614 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359459, d361614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359459, d361614, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359510 q = 0) : d361665 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359510, d361665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37698 q selected
    | true =>
      simp only [d359510, d361665, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37680 q selected
  have h9 (q : Pattern) (selected : d359555 q = 0) : d361579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359555, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37705 q selected
    | true =>
      simp only [d359555, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37706 q selected
  have h10 (q : Pattern) (selected : d359556 q = 0) : d361666 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359556, d361666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359556, d361666, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359561 q = 0) : d361671 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359561, d361671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37707 q selected
    | true =>
      simp only [d359561, d361671, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359562 q = 0) : d361672 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359562, d361672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359562, d361672, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359563 q = 0) : d361673 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359563, d361673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359563, d361673, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359564 q = 0) : d361674 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359564, d361674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359564, d361674, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359565 q = 0) : d361675 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359565, d361675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359565, d361675, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359569 q = 0) : d361679 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359569, d361679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37709 q selected
    | true =>
      simp only [d359569, d361679, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37710 q selected
  have h17 (q : Pattern) (selected : d359570 q = 0) : d361680 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359570, d361680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359570, d361680, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
  have h18 (q : Pattern) (selected : d359571 q = 0) : d361681 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359571, d361681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359571, d361681, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h19 (q : Pattern) (selected : d359572 q = 0) : d361682 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359572, d361682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359572, d361682, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d359575 q = 0) : d361685 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359575, d361685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37711 q selected
    | true =>
      simp only [d359575, d361685, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37712 q selected
  have h21 (q : Pattern) (selected : d359576 q = 0) : d361686 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359576, d361686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359576, d361686, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
  have h22 (q : Pattern) (selected : d359577 q = 0) : d361687 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359577, d361687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359577, d361687, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d359579 q = 0) : d361689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359579, d361689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37713 q selected
    | true =>
      simp only [d359579, d361689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37683 q selected
  have h24 (q : Pattern) (selected : d359582 q = 0) : d361589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359582, d361589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37714 q selected
    | true =>
      simp only [d359582, d361589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37715 q selected
  have h25 (q : Pattern) (selected : d359583 q = 0) : d361690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359583, d361690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
    | true =>
      simp only [d359583, d361690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
  have h26 (q : Pattern) (selected : d359585 q = 0) : d361692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359585, d361692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37716 q selected
    | true =>
      simp only [d359585, d361692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h27 (q : Pattern) (selected : d359586 q = 0) : d361693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359586, d361693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
    | true =>
      simp only [d359586, d361693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h28 (q : Pattern) (selected : d359587 q = 0) : d361694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359587, d361694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
    | true =>
      simp only [d359587, d361694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h27 q selected
  have h29 (q : Pattern) (selected : d359588 q = 0) : d361695 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359588, d361695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d359588, d361695, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h28 q selected
  have h30 (q : Pattern) (selected : d359589 q = 0) : d361696 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359589, d361696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359589, d361696, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h29 q selected
  have h31 (q : Pattern) (selected : d359590 q = 0) : d361697 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359590, d361697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359590, d361697, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h30 q selected
  exact h31 p selected
theorem eqIntro37718 (p : Pattern) (selected : d359597 p = 0) : d361704 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359424 q = 0) : d361579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359424, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37680 q selected
    | true =>
      simp only [d359424, d361579, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37681 q selected
  have h2 (q : Pattern) (selected : d359425 q = 0) : d361580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359425, d361580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359425, d361580, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359426 q = 0) : d361581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359426, d361581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359426, d361581, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359427 q = 0) : d361582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359427, d361582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359427, d361582, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359428 q = 0) : d361583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359428, d361583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359428, d361583, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359592 q = 0) : d361699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359592, d361699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37681 q selected
    | true =>
      simp only [d359592, d361699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359593 q = 0) : d361700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359593, d361700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359593, d361700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359594 q = 0) : d361701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359594, d361701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359594, d361701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359595 q = 0) : d361702 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359595, d361702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359595, d361702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359596 q = 0) : d361703 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359596, d361703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359596, d361703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359597 q = 0) : d361704 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359597, d361704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359597, d361704, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37719 (p : Pattern) (selected : d359603 p = 0) : d361710 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359592 q = 0) : d361699 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359592, d361699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37681 q selected
    | true =>
      simp only [d359592, d361699, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359593 q = 0) : d361700 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359593, d361700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359593, d361700, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359594 q = 0) : d361701 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359594, d361701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359594, d361701, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359595 q = 0) : d361702 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359595, d361702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359595, d361702, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359596 q = 0) : d361703 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359596, d361703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359596, d361703, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359598 q = 0) : d361705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359598, d361705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37684 q selected
    | true =>
      simp only [d359598, d361705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359599 q = 0) : d361706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359599, d361706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359599, d361706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359600 q = 0) : d361707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359600, d361707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359600, d361707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359601 q = 0) : d361708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359601, d361708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359601, d361708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359602 q = 0) : d361709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359602, d361709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359602, d361709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359603 q = 0) : d361710 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359603, d361710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359603, d361710, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37720 (p : Pattern) (selected : d359610 p = 0) : d361717 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359579 q = 0) : d361689 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359579, d361689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37713 q selected
    | true =>
      simp only [d359579, d361689, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37683 q selected
  have h2 (q : Pattern) (selected : d359582 q = 0) : d361589 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359582, d361589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37714 q selected
    | true =>
      simp only [d359582, d361589, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37715 q selected
  have h3 (q : Pattern) (selected : d359583 q = 0) : d361690 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359583, d361690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359583, d361690, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359585 q = 0) : d361692 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359585, d361692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37716 q selected
    | true =>
      simp only [d359585, d361692, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359586 q = 0) : d361693 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359586, d361693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359586, d361693, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359587 q = 0) : d361694 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359587, d361694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359587, d361694, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359608 q = 0) : d361715 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359608, d361715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359608, d361715, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359609 q = 0) : d361716 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359609, d361716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359609, d361716, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359610 q = 0) : d361717 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359610, d361717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359610, d361717, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37721 (p : Pattern) (selected : d359612 p = 0) : d361719 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359598 q = 0) : d361705 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359598, d361705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37684 q selected
    | true =>
      simp only [d359598, d361705, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359599 q = 0) : d361706 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359599, d361706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359599, d361706, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359600 q = 0) : d361707 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359600, d361707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359600, d361707, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359601 q = 0) : d361708 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359601, d361708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359601, d361708, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359602 q = 0) : d361709 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359602, d361709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359602, d361709, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359612 q = 0) : d361719 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359612, d361719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359612, d361719, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37722 (p : Pattern) (selected : d359632 p = 0) : d361739 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359618 q = 0) : d361725 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359618, d361725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359618, d361725, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37692 q selected
  have h2 (q : Pattern) (selected : d359475 q = 0) : d361630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359475, d361630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37692 q selected
    | true =>
      simp only [d359475, d361630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359619 q = 0) : d361726 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359619, d361726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359619, d361726, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359476 q = 0) : d361631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359476, d361631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359476, d361631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359620 q = 0) : d361727 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359620, d361727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359620, d361727, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359621 q = 0) : d361728 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359621, d361728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359621, d361728, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359622 q = 0) : d361729 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359622, d361729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359622, d361729, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37693 q selected
  have h8 (q : Pattern) (selected : d359480 q = 0) : d361635 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359480, d361635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37693 q selected
    | true =>
      simp only [d359480, d361635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359623 q = 0) : d361730 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359623, d361730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359623, d361730, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359481 q = 0) : d361636 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359481, d361636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359481, d361636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359624 q = 0) : d361731 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359624, d361731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359624, d361731, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359625 q = 0) : d361732 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359625, d361732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359625, d361732, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359626 q = 0) : d361733 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359626, d361733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359626, d361733, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359627 q = 0) : d361734 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359627, d361734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359627, d361734, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37694 q selected
  have h15 (q : Pattern) (selected : d359488 q = 0) : d361643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359488, d361643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37694 q selected
    | true =>
      simp only [d359488, d361643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359628 q = 0) : d361735 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359628, d361735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359628, d361735, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359489 q = 0) : d361644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359489, d361644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359489, d361644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359629 q = 0) : d361736 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359629, d361736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359629, d361736, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359630 q = 0) : d361737 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359630, d361737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d359630, d361737, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d359340 q = 0) : d361514 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359340, d361514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359340, d361514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
  have h21 (q : Pattern) (selected : d359240 q = 0) : d361444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
    | true =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d359341 q = 0) : d361515 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359341, d361515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d359341, d361515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d359241 q = 0) : d361445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d359342 q = 0) : d361516 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359342, d361516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d359342, d361516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d359343 q = 0) : d361517 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359343, d361517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d359343, d361517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d359631 q = 0) : d361738 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359631, d361738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359631, d361738, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d359632 q = 0) : d361739 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359632, d361739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359632, d361739, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro37723 (p : Pattern) (selected : d359636 p = 0) : d361743 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359340 q = 0) : d361514 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359340, d361514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359340, d361514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
  have h2 (q : Pattern) (selected : d359240 q = 0) : d361444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37647 q selected
    | true =>
      simp only [d359240, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359341 q = 0) : d361515 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359341, d361515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359341, d361515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359241 q = 0) : d361445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359241, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359342 q = 0) : d361516 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359342, d361516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359342, d361516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359343 q = 0) : d361517 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359343, d361517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359343, d361517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d358988 q = 0) : d361241 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358988, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d358988, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
  have h8 (q : Pattern) (selected : d358947 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37598 q selected
    | true =>
      simp only [d358947, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d358989 q = 0) : d361242 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358989, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d358989, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d358948 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d358948, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d358990 q = 0) : d361243 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d358990, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d358990, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d358991 q = 0) : d361244 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d358991, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d358991, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359344 q = 0) : d361518 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359344, d361518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359344, d361518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d358992 q = 0) : d361245 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d358992, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d358992, d361245, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359636 q = 0) : d361743 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359636, d361743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359636, d361743, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  exact h15 p selected
theorem eqIntro37724 (p : Pattern) (selected : d359642 p = 0) : d361749 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359633 q = 0) : d361740 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359633, d361740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37722 q selected
    | true =>
      simp only [d359633, d361740, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37667 q selected
  have h2 (q : Pattern) (selected : d359634 q = 0) : d361741 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359634, d361741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359634, d361741, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359635 q = 0) : d361742 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359635, d361742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359635, d361742, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359637 q = 0) : d361744 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359637, d361744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37667 q selected
    | true =>
      simp only [d359637, d361744, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37723 q selected
  have h5 (q : Pattern) (selected : d359638 q = 0) : d361745 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359638, d361745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359638, d361745, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359639 q = 0) : d361746 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359639, d361746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359639, d361746, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359640 q = 0) : d361747 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359640, d361747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359640, d361747, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359346 q = 0) : d361520 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359346, d361520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37667 q selected
    | true =>
      simp only [d359346, d361520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37633 q selected
  have h9 (q : Pattern) (selected : d359347 q = 0) : d361521 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359347, d361521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359347, d361521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359348 q = 0) : d361522 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359348, d361522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359348, d361522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359148 q = 0) : d361371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37633 q selected
    | true =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37606 q selected
  have h12 (q : Pattern) (selected : d359149 q = 0) : d361372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359150 q = 0) : d361373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359349 q = 0) : d361523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359349, d361523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359349, d361523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
  have h15 (q : Pattern) (selected : d359641 q = 0) : d361748 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359641, d361748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359641, d361748, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
  have h16 (q : Pattern) (selected : d359642 q = 0) : d361749 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359642, d361749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359642, d361749, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h16 p selected
theorem eqIntro37725 (p : Pattern) (selected : d359647 p = 0) : d361754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359346 q = 0) : d361520 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359346, d361520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37667 q selected
    | true =>
      simp only [d359346, d361520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37633 q selected
  have h2 (q : Pattern) (selected : d359347 q = 0) : d361521 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359347, d361521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359347, d361521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359348 q = 0) : d361522 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359348, d361522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359348, d361522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359148 q = 0) : d361371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37633 q selected
    | true =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37606 q selected
  have h5 (q : Pattern) (selected : d359149 q = 0) : d361372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359150 q = 0) : d361373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359349 q = 0) : d361523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359349, d361523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359349, d361523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359645 q = 0) : d361752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359645, d361752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359645, d361752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359646 q = 0) : d361753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359646, d361753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359646, d361753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359647 q = 0) : d361754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359647, d361754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359647, d361754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37726 (p : Pattern) (selected : d359653 p = 0) : d361760 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359643 q = 0) : d361750 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359643, d361750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37724 q selected
    | true =>
      simp only [d359643, d361750, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359644 q = 0) : d361751 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359644, d361751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359644, d361751, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359648 q = 0) : d361755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359648, d361755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37725 q selected
    | true =>
      simp only [d359648, d361755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359649 q = 0) : d361756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359649, d361756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359649, d361756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359650 q = 0) : d361757 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359650, d361757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359650, d361757, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359651 q = 0) : d361758 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359651, d361758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359651, d361758, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359652 q = 0) : d361759 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359652, d361759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359652, d361759, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359653 q = 0) : d361760 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359653, d361760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359653, d361760, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37727 (p : Pattern) (selected : d359655 p = 0) : d361762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359148 q = 0) : d361371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37633 q selected
    | true =>
      simp only [d359148, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37606 q selected
  have h2 (q : Pattern) (selected : d359149 q = 0) : d361372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359149, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359150 q = 0) : d361373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359150, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359645 q = 0) : d361752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359645, d361752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359645, d361752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359654 q = 0) : d361761 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359654, d361761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359654, d361761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359655 q = 0) : d361762 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359655, d361762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359655, d361762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37728 (p : Pattern) (selected : d359661 p = 0) : d361768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359648 q = 0) : d361755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359648, d361755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37725 q selected
    | true =>
      simp only [d359648, d361755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359649 q = 0) : d361756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359649, d361756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359649, d361756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359656 q = 0) : d361763 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359656, d361763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37727 q selected
    | true =>
      simp only [d359656, d361763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359657 q = 0) : d361764 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359657, d361764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359657, d361764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359658 q = 0) : d361765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359658, d361765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359658, d361765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359659 q = 0) : d361766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359659, d361766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359659, d361766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359660 q = 0) : d361767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359660, d361767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359660, d361767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359661 q = 0) : d361768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359661, d361768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359661, d361768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37729 (p : Pattern) (selected : d359673 p = 0) : d361519 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359663 q = 0) : d361509 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359663, d361509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359663, d361509, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37700 q selected
  have h2 (q : Pattern) (selected : d359520 q = 0) : d361436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359520, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37700 q selected
    | true =>
      simp only [d359520, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359664 q = 0) : d361510 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359664, d361510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359664, d361510, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359521 q = 0) : d361437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359521, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359521, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359665 q = 0) : d361511 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359665, d361511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359665, d361511, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359666 q = 0) : d361512 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359666, d361512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359666, d361512, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359359 q = 0) : d361365 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359359, d361365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359359, d361365, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37652 q selected
  have h8 (q : Pattern) (selected : d359268 q = 0) : d361311 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359268, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37652 q selected
    | true =>
      simp only [d359268, d361311, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359360 q = 0) : d361366 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359360, d361366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359360, d361366, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359269 q = 0) : d361312 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359269, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359269, d361312, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359361 q = 0) : d361367 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359361, d361367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359361, d361367, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  have h12 (q : Pattern) (selected : d359362 q = 0) : d361368 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359362, d361368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359362, d361368, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h13 (q : Pattern) (selected : d359667 q = 0) : d361513 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359667, d361513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359667, d361513, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359668 q = 0) : d361514 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359668, d361514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359668, d361514, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37701 q selected
  have h15 (q : Pattern) (selected : d359528 q = 0) : d361444 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359528, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37701 q selected
    | true =>
      simp only [d359528, d361444, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359669 q = 0) : d361515 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359669, d361515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359669, d361515, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359529 q = 0) : d361445 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359529, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
    | true =>
      simp only [d359529, d361445, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359670 q = 0) : d361516 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359670, d361516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359670, d361516, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359671 q = 0) : d361517 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359671, d361517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
    | true =>
      simp only [d359671, d361517, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h20 (q : Pattern) (selected : d359161 q = 0) : d361241 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359161, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359161, d361241, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
  have h21 (q : Pattern) (selected : d359086 q = 0) : d361200 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37621 q selected
    | true =>
      simp only [d359086, d361200, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d359162 q = 0) : d361242 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359162, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d359162, d361242, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
  have h23 (q : Pattern) (selected : d359087 q = 0) : d361201 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359087, d361201, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h24 (q : Pattern) (selected : d359163 q = 0) : d361243 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359163, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
    | true =>
      simp only [d359163, d361243, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h23 q selected
  have h25 (q : Pattern) (selected : d359164 q = 0) : d361244 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359164, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h24 q selected
    | true =>
      simp only [d359164, d361244, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h26 (q : Pattern) (selected : d359672 q = 0) : d361518 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359672, d361518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359672, d361518, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h25 q selected
  have h27 (q : Pattern) (selected : d359673 q = 0) : d361519 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359673, d361519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359673, d361519, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h26 q selected
  exact h27 p selected
theorem eqIntro37730 (p : Pattern) (selected : d359680 p = 0) : d361754 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359674 q = 0) : d361520 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359674, d361520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37729 q selected
    | true =>
      simp only [d359674, d361520, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37670 q selected
  have h2 (q : Pattern) (selected : d359675 q = 0) : d361521 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359675, d361521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359675, d361521, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359676 q = 0) : d361522 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359676, d361522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359676, d361522, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359365 q = 0) : d361371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359365, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37670 q selected
    | true =>
      simp only [d359365, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37636 q selected
  have h5 (q : Pattern) (selected : d359366 q = 0) : d361372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359366, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359366, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359367 q = 0) : d361373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359367, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359367, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359677 q = 0) : d361523 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359677, d361523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359677, d361523, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359678 q = 0) : d361752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359678, d361752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359678, d361752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359679 q = 0) : d361753 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359679, d361753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359679, d361753, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359680 q = 0) : d361754 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359680, d361754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359680, d361754, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37731 (p : Pattern) (selected : d359684 p = 0) : d361762 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359365 q = 0) : d361371 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359365, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37670 q selected
    | true =>
      simp only [d359365, d361371, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37636 q selected
  have h2 (q : Pattern) (selected : d359366 q = 0) : d361372 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359366, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359366, d361372, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359367 q = 0) : d361373 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359367, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359367, d361373, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359678 q = 0) : d361752 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359678, d361752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359678, d361752, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359683 q = 0) : d361761 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359683, d361761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359683, d361761, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359684 q = 0) : d361762 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359684, d361762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359684, d361762, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37732 (p : Pattern) (selected : d359690 p = 0) : d361768 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359681 q = 0) : d361755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359681, d361755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37730 q selected
    | true =>
      simp only [d359681, d361755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359682 q = 0) : d361756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359682, d361756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359682, d361756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359685 q = 0) : d361763 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359685, d361763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37731 q selected
    | true =>
      simp only [d359685, d361763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359686 q = 0) : d361764 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359686, d361764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359686, d361764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359687 q = 0) : d361765 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359687, d361765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359687, d361765, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359688 q = 0) : d361766 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359688, d361766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359688, d361766, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359689 q = 0) : d361767 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359689, d361767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359689, d361767, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359690 q = 0) : d361768 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359690, d361768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359690, d361768, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
theorem eqIntro37733 (p : Pattern) (selected : d359694 p = 0) : d361773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359685 q = 0) : d361763 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359685, d361763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37731 q selected
    | true =>
      simp only [d359685, d361763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359686 q = 0) : d361764 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359686, d361764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359686, d361764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359691 q = 0) : d361770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359691, d361770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359691, d361770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359692 q = 0) : d361771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359692, d361771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359692, d361771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359693 q = 0) : d361772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359693, d361772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359693, d361772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359694 q = 0) : d361773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359694, d361773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359694, d361773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37734 (p : Pattern) (selected : d359700 p = 0) : d361779 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359648 q = 0) : d361755 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359648, d361755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37725 q selected
    | true =>
      simp only [d359648, d361755, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359649 q = 0) : d361756 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359649, d361756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359649, d361756, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359697 q = 0) : d361776 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359697, d361776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359697, d361776, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359698 q = 0) : d361777 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359698, d361777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359698, d361777, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359699 q = 0) : d361778 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359699, d361778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359699, d361778, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359700 q = 0) : d361779 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359700, d361779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359700, d361779, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37735 (p : Pattern) (selected : d359706 p = 0) : d361785 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359662 q = 0) : d361769 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359662, d361769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37726 q selected
    | true =>
      simp only [d359662, d361769, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37728 q selected
  have h2 (q : Pattern) (selected : d359695 q = 0) : d361774 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359695, d361774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37732 q selected
    | true =>
      simp only [d359695, d361774, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37733 q selected
  have h3 (q : Pattern) (selected : d359696 q = 0) : d361775 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359696, d361775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359696, d361775, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359701 q = 0) : d361780 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359701, d361780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37734 q selected
    | true =>
      simp only [d359701, d361780, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359702 q = 0) : d361781 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359702, d361781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359702, d361781, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359703 q = 0) : d361782 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359703, d361782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359703, d361782, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359704 q = 0) : d361783 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359704, d361783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359704, d361783, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359705 q = 0) : d361784 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359705, d361784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359705, d361784, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359706 q = 0) : d361785 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359706, d361785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359706, d361785, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  exact h9 p selected
theorem eqIntro37736 (p : Pattern) (selected : d359711 p = 0) : d361773 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359656 q = 0) : d361763 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359656, d361763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37727 q selected
    | true =>
      simp only [d359656, d361763, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359657 q = 0) : d361764 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359657, d361764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359657, d361764, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359708 q = 0) : d361770 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359708, d361770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359708, d361770, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359709 q = 0) : d361771 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359709, d361771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359709, d361771, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359710 q = 0) : d361772 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359710, d361772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359710, d361772, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359711 q = 0) : d361773 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359711, d361773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359711, d361773, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37737 (p : Pattern) (selected : d359717 p = 0) : d361792 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359712 q = 0) : d361787 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359712, d361787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37736 q selected
    | true =>
      simp only [d359712, d361787, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359713 q = 0) : d361788 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359713, d361788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359713, d361788, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359714 q = 0) : d361789 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359714, d361789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359714, d361789, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359715 q = 0) : d361790 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359715, d361790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359715, d361790, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359716 q = 0) : d361791 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359716, d361791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359716, d361791, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359717 q = 0) : d361792 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359717, d361792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359717, d361792, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37738 (p : Pattern) (selected : d359723 p = 0) : d361798 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359430 q = 0) : d361585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359430, d361585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359430, d361585, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37682 q selected
  have h2 (q : Pattern) (selected : d359431 q = 0) : d361586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359431, d361586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359431, d361586, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359440 q = 0) : d361595 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359440, d361595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37682 q selected
    | true =>
      simp only [d359440, d361595, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37685 q selected
  have h4 (q : Pattern) (selected : d359441 q = 0) : d361596 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359441, d361596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359441, d361596, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359442 q = 0) : d361597 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359442, d361597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359442, d361597, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359591 q = 0) : d361698 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359591, d361698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37708 q selected
    | true =>
      simp only [d359591, d361698, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37717 q selected
  have h7 (q : Pattern) (selected : d359604 q = 0) : d361711 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359604, d361711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37718 q selected
    | true =>
      simp only [d359604, d361711, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37719 q selected
  have h8 (q : Pattern) (selected : d359605 q = 0) : d361712 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359605, d361712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359605, d361712, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  have h9 (q : Pattern) (selected : d359606 q = 0) : d361713 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359606, d361713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359606, d361713, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h10 (q : Pattern) (selected : d359607 q = 0) : d361714 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359607, d361714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359607, d361714, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
  have h11 (q : Pattern) (selected : d359611 q = 0) : d361718 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359611, d361718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359611, d361718, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37720 q selected
  have h12 (q : Pattern) (selected : d359613 q = 0) : d361720 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359613, d361720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359613, d361720, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37721 q selected
  have h13 (q : Pattern) (selected : d359614 q = 0) : d361721 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359614, d361721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
    | true =>
      simp only [d359614, d361721, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
  have h14 (q : Pattern) (selected : d359615 q = 0) : d361722 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359615, d361722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359615, d361722, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359616 q = 0) : d361723 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359616, d361723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359616, d361723, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359617 q = 0) : d361724 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359617, d361724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359617, d361724, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359707 q = 0) : d361786 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359707, d361786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359707, d361786, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37735 q selected
  have h18 (q : Pattern) (selected : d359718 q = 0) : d361793 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d359718, d361793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359718, d361793, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37737 q selected
  have h19 (q : Pattern) (selected : d359719 q = 0) : d361794 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d359719, d361794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
    | true =>
      simp only [d359719, d361794, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  have h20 (q : Pattern) (selected : d359720 q = 0) : d361795 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d359720, d361795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h19 q selected
    | true =>
      simp only [d359720, d361795, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h21 (q : Pattern) (selected : d359721 q = 0) : d361796 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d359721, d361796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h20 q selected
    | true =>
      simp only [d359721, d361796, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h22 (q : Pattern) (selected : d359722 q = 0) : d361797 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d359722, d361797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h21 q selected
    | true =>
      simp only [d359722, d361797, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h23 (q : Pattern) (selected : d359723 q = 0) : d361798 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d359723, d361798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359723, d361798, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h22 q selected
  exact h23 p selected
theorem eqIntro37739 (p : Pattern) (selected : d359729 p = 0) : d361804 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359724 q = 0) : d361799 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d359724, d361799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359724, d361799, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37738 q selected
  have h2 (q : Pattern) (selected : d359725 q = 0) : d361800 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d359725, d361800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359725, d361800, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359726 q = 0) : d361801 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d359726, d361801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359726, d361801, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359727 q = 0) : d361802 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d359727, d361802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359727, d361802, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359728 q = 0) : d361803 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d359728, d361803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359728, d361803, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359729 q = 0) : d361804 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d359729, d361804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359729, d361804, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37740 (p : Pattern) (selected : d359731 p = 0) : d361806 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359052 q = 0) : d361305 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37615 q selected
    | true =>
      simp only [d359052, d361305, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359053 q = 0) : d361306 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359053, d361306, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d358941 q = 0) : d361194 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37597 q selected
    | true =>
      simp only [d358941, d361194, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d358942 q = 0) : d361195 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d358942, d361195, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359054 q = 0) : d361307 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359054, d361307, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d358943 q = 0) : d361196 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d358943, d361196, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359055 q = 0) : d361308 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d359055, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359055, d361308, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359056 q = 0) : d361309 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d359056, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359056, d361309, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359731 q = 0) : d361806 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d359731, d361806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359731, d361806, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h9 p selected
theorem eqIntro37741 (p : Pattern) (selected : d359737 p = 0) : d361812 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359475 q = 0) : d361630 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359475, d361630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37692 q selected
    | true =>
      simp only [d359475, d361630, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359476 q = 0) : d361631 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359476, d361631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359476, d361631, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359477 q = 0) : d361632 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359477, d361632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359477, d361632, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359478 q = 0) : d361633 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359478, d361633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359478, d361633, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359480 q = 0) : d361635 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359480, d361635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37693 q selected
    | true =>
      simp only [d359480, d361635, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359481 q = 0) : d361636 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359481, d361636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359481, d361636, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359482 q = 0) : d361637 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359482, d361637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359482, d361637, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359483 q = 0) : d361638 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359483, d361638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359483, d361638, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359484 q = 0) : d361639 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359484, d361639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359484, d361639, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359488 q = 0) : d361643 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359488, d361643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37694 q selected
    | true =>
      simp only [d359488, d361643, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359489 q = 0) : d361644 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359489, d361644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
    | true =>
      simp only [d359489, d361644, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h12 (q : Pattern) (selected : d359490 q = 0) : d361645 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359490, d361645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359490, d361645, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h11 q selected
  have h13 (q : Pattern) (selected : d359491 q = 0) : d361646 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359491, d361646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h12 q selected
    | true =>
      simp only [d359491, d361646, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h14 (q : Pattern) (selected : d359732 q = 0) : d361807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359732, d361807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37740 q selected
    | true =>
      simp only [d359732, d361807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h15 (q : Pattern) (selected : d359733 q = 0) : d361808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359733, d361808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h14 q selected
    | true =>
      simp only [d359733, d361808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h16 (q : Pattern) (selected : d359734 q = 0) : d361809 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359734, d361809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359734, d361809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h15 q selected
  have h17 (q : Pattern) (selected : d359735 q = 0) : d361810 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359735, d361810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h16 q selected
    | true =>
      simp only [d359735, d361810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h18 (q : Pattern) (selected : d359736 q = 0) : d361811 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359736, d361811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h13 q selected
    | true =>
      simp only [d359736, d361811, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h17 q selected
  have h19 (q : Pattern) (selected : d359737 q = 0) : d361812 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359737, d361812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359737, d361812, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h18 q selected
  exact h19 p selected
theorem eqIntro37742 (p : Pattern) (selected : d359740 p = 0) : d361815 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359232 q = 0) : d361436 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359232, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37646 q selected
    | true =>
      simp only [d359232, d361436, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359233 q = 0) : d361437 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359233, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359233, d361437, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359234 q = 0) : d361438 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359234, d361438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359234, d361438, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359235 q = 0) : d361439 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359235, d361439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359235, d361439, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359732 q = 0) : d361807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359732, d361807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37740 q selected
    | true =>
      simp only [d359732, d361807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359733 q = 0) : d361808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359733, d361808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359733, d361808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359734 q = 0) : d361809 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359734, d361809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359734, d361809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359735 q = 0) : d361810 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359735, d361810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359735, d361810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359738 q = 0) : d361813 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359738, d361813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359738, d361813, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359739 q = 0) : d361814 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359739, d361814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
    | true =>
      simp only [d359739, d361814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h11 (q : Pattern) (selected : d359740 q = 0) : d361815 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359740, d361815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359740, d361815, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h10 q selected
  exact h11 p selected
theorem eqIntro37743 (p : Pattern) (selected : d359744 p = 0) : d361819 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359732 q = 0) : d361807 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d359732, d361807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37740 q selected
    | true =>
      simp only [d359732, d361807, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359733 q = 0) : d361808 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d359733, d361808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
    | true =>
      simp only [d359733, d361808, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h3 (q : Pattern) (selected : d359734 q = 0) : d361809 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d359734, d361809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359734, d361809, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359735 q = 0) : d361810 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d359735, d361810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359735, d361810, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359739 q = 0) : d361814 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d359739, d361814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359739, d361814, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359744 q = 0) : d361819 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d359744, d361819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359744, d361819, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37744 (p : Pattern) (selected : d359751 p = 0) : d361826 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359741 q = 0) : d361816 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359741, d361816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37741 q selected
    | true =>
      simp only [d359741, d361816, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37742 q selected
  have h2 (q : Pattern) (selected : d359742 q = 0) : d361817 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359742, d361817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359742, d361817, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359743 q = 0) : d361818 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359743, d361818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359743, d361818, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359745 q = 0) : d361820 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359745, d361820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37742 q selected
    | true =>
      simp only [d359745, d361820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37743 q selected
  have h5 (q : Pattern) (selected : d359746 q = 0) : d361821 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359746, d361821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359746, d361821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359747 q = 0) : d361822 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359747, d361822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359747, d361822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  have h7 (q : Pattern) (selected : d359748 q = 0) : d361823 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359748, d361823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359748, d361823, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
  have h8 (q : Pattern) (selected : d359749 q = 0) : d361824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359749, d361824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359749, d361824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h9 (q : Pattern) (selected : d359750 q = 0) : d361825 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359750, d361825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359750, d361825, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h8 q selected
  have h10 (q : Pattern) (selected : d359751 q = 0) : d361826 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359751, d361826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h9 q selected
    | true =>
      simp only [d359751, d361826, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h10 p selected
theorem eqIntro37745 (p : Pattern) (selected : d359755 p = 0) : d361830 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359745 q = 0) : d361820 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d359745, d361820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37742 q selected
    | true =>
      simp only [d359745, d361820, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37743 q selected
  have h2 (q : Pattern) (selected : d359746 q = 0) : d361821 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d359746, d361821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359746, d361821, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359747 q = 0) : d361822 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d359747, d361822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359747, d361822, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
  have h4 (q : Pattern) (selected : d359749 q = 0) : d361824 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d359749, d361824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359749, d361824, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359754 q = 0) : d361829 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d359754, d361829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359754, d361829, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359755 q = 0) : d361830 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d359755, d361830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359755, d361830, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h6 p selected
theorem eqIntro37746 (p : Pattern) (selected : d359761 p = 0) : d361836 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359752 q = 0) : d361827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359752, d361827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37744 q selected
    | true =>
      simp only [d359752, d361827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359753 q = 0) : d361828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359753, d361828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359753, d361828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359756 q = 0) : d361831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359756, d361831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37745 q selected
    | true =>
      simp only [d359756, d361831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359757 q = 0) : d361832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359757, d361832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359757, d361832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359758 q = 0) : d361833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359758, d361833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359758, d361833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359759 q = 0) : d361834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359759, d361834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359759, d361834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359760 q = 0) : d361835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359760, d361835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359760, d361835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359761 q = 0) : d361836 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359761, d361836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359761, d361836, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
  exact h8 p selected
theorem eqIntro37747 (p : Pattern) (selected : d359765 p = 0) : d361840 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359756 q = 0) : d361831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359756, d361831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37745 q selected
    | true =>
      simp only [d359756, d361831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359757 q = 0) : d361832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359757, d361832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359757, d361832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359762 q = 0) : d361837 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359762, d361837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359762, d361837, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359763 q = 0) : d361838 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359763, d361838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
    | true =>
      simp only [d359763, d361838, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h5 (q : Pattern) (selected : d359764 q = 0) : d361839 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359764, d361839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
    | true =>
      simp only [d359764, d361839, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h6 (q : Pattern) (selected : d359765 q = 0) : d361840 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359765, d361840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359765, d361840, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37748 (p : Pattern) (selected : d359771 p = 0) : d361846 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359766 q = 0) : d361841 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d359766, d361841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37746 q selected
    | true =>
      simp only [d359766, d361841, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37747 q selected
  have h2 (q : Pattern) (selected : d359767 q = 0) : d361842 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d359767, d361842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359767, d361842, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359768 q = 0) : d361843 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d359768, d361843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359768, d361843, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359769 q = 0) : d361844 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d359769, d361844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359769, d361844, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359770 q = 0) : d361845 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d359770, d361845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359770, d361845, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359771 q = 0) : d361846 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d359771, d361846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359771, d361846, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
  exact h6 p selected
theorem eqIntro37749 (p : Pattern) (selected : d359774 p = 0) : d361849 p = 1 := by
  have h0 (q : Pattern) (selected : d0 q = 0) : d1 q = 1 := by
    rfl
  have h1 (q : Pattern) (selected : d359752 q = 0) : d361827 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359752, d361827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37744 q selected
    | true =>
      simp only [d359752, d361827, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h2 (q : Pattern) (selected : d359753 q = 0) : d361828 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359753, d361828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359753, d361828, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h1 q selected
  have h3 (q : Pattern) (selected : d359756 q = 0) : d361831 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d359756, d361831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact eqIntro37745 q selected
    | true =>
      simp only [d359756, d361831, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h4 (q : Pattern) (selected : d359757 q = 0) : d361832 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d359757, d361832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
    | true =>
      simp only [d359757, d361832, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h3 q selected
  have h5 (q : Pattern) (selected : d359758 q = 0) : d361833 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d359758, d361833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h2 q selected
    | true =>
      simp only [d359758, d361833, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h4 q selected
  have h6 (q : Pattern) (selected : d359759 q = 0) : d361834 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d359759, d361834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h5 q selected
    | true =>
      simp only [d359759, d361834, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h7 (q : Pattern) (selected : d359760 q = 0) : d361835 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d359760, d361835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h6 q selected
    | true =>
      simp only [d359760, d361835, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  have h8 (q : Pattern) (selected : d359774 q = 0) : d361849 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d359774, d361849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h7 q selected
    | true =>
      simp only [d359774, d361849, bit, Bool.false_eq_true, ↓reduceIte] at selected ⊢
      all_goals
        exact h0 q selected
  exact h8 p selected
end NetHack.Soko22Hazard87
