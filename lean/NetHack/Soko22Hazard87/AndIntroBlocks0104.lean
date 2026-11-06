import NetHack.Soko22Hazard87.AndIntroBlocks0103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro26000 (p : Pattern) (ha : d112760 p = 1) (hb : d141373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112698 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
    | true =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d112749 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112749, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112749, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112750 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112750, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112750, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112751 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112751, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112751, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112752 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112752, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112752, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112705 q = 1) (hb : d141318 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25992 q ha hb
    | true =>
      simp only [d112705, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h7 (q : Pattern) (ha : d112756 q = 1) (hb : d141369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112756, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112756, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112757 q = 1) (hb : d141370 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112757, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112757, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112758 q = 1) (hb : d141371 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112758, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112758, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112759 q = 1) (hb : d141372 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112759, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112759, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112760 q = 1) (hb : d141373 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112760, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112760, d141373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26001 (p : Pattern) (ha : d112765 p = 1) (hb : d141378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112695 q = 1) (hb : d141308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112695, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112695, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112764 q = 1) (hb : d141377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112764, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112764, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112765 q = 1) (hb : d141378 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112765, d141378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112765, d141378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26002 (p : Pattern) (ha : d112772 p = 1) (hb : d141385 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112770 q = 1) (hb : d141383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112770, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112770, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112771 q = 1) (hb : d141384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112771, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112771, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112772 q = 1) (hb : d141385 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112772, d141385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112772, d141385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26003 (p : Pattern) (ha : d112782 p = 1) (hb : d141391 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112777 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112777, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18535 q hb ha
    | true =>
      simp only [d112777, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112778 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112778, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112778, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112779 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112779, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112779, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d68915 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
    | true =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68916 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68917 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112780 q = 1) (hb : d141389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112780, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112780, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d31 q = 1) (hb : d51883 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro3 q ha hb
    | true =>
      simp only [d31, d51883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d32 q = 1) (hb : d51884 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d32, d51884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d33 q = 1) (hb : d51885 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d33, d51885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112689 q = 1) (hb : d141302 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112689, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112689, d141302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112781 q = 1) (hb : d141390 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112781, d141390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112781, d141390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112782 q = 1) (hb : d141391 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112782, d141391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d112782, d141391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro26004 (p : Pattern) (ha : d112788 p = 1) (hb : d141397 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112783 q = 1) (hb : d141392 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112783, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26003 q ha hb
    | true =>
      simp only [d112783, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112784 q = 1) (hb : d141393 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112784, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112784, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112785 q = 1) (hb : d141394 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112785, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112785, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112786 q = 1) (hb : d141395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112786, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112786, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112787 q = 1) (hb : d141396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112787, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112787, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112788 q = 1) (hb : d141397 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112788, d141397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112788, d141397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26005 (p : Pattern) (ha : d112794 p = 1) (hb : d141403 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112791 q = 1) (hb : d141400 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112791, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112791, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112792 q = 1) (hb : d141401 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112792, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112792, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112793 q = 1) (hb : d141402 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112793, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112793, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112794 q = 1) (hb : d141403 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112794, d141403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112794, d141403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26006 (p : Pattern) (ha : d112800 p = 1) (hb : d141409 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112766 q = 1) (hb : d141379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112766, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26001 q ha hb
    | true =>
      simp only [d112766, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d112767 q = 1) (hb : d141380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112767, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112767, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112768 q = 1) (hb : d141381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112768, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112768, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112769 q = 1) (hb : d141382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112769, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112769, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112773 q = 1) (hb : d141386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112773, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26002 q ha hb
    | true =>
      simp only [d112773, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d112774 q = 1) (hb : d141387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112774, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112774, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112775 q = 1) (hb : d141388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112775, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112775, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112789 q = 1) (hb : d141398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112789, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26004 q ha hb
    | true =>
      simp only [d112789, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112790 q = 1) (hb : d141399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112790, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112795 q = 1) (hb : d141404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112795, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26005 q ha hb
    | true =>
      simp only [d112795, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112796 q = 1) (hb : d141405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112796, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112796, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112797 q = 1) (hb : d141406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112797, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112798 q = 1) (hb : d141407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112798, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112799 q = 1) (hb : d141408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112799, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112800 q = 1) (hb : d141409 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112800, d141409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112800, d141409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26007 (p : Pattern) (ha : d112801 p = 1) (hb : d141410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112695 q = 1) (hb : d141308 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112695, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112695, d141308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112764 q = 1) (hb : d141377 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112764, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112764, d141377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112801 q = 1) (hb : d141410 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112801, d141410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112801, d141410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26008 (p : Pattern) (ha : d112806 p = 1) (hb : d141415 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d37 q = 1) (hb : d51889 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro4 q ha hb
    | true =>
      simp only [d37, d51889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d38 q = 1) (hb : d51890 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d38, d51890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112694 q = 1) (hb : d141307 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112694, d141307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d112770 q = 1) (hb : d141383 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112770, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112770, d141383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112771 q = 1) (hb : d141384 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112771, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112771, d141384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112806 q = 1) (hb : d141415 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112806, d141415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112806, d141415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26009 (p : Pattern) (ha : d112810 p = 1) (hb : d141419 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112783 q = 1) (hb : d141392 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112783, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26003 q ha hb
    | true =>
      simp only [d112783, d141392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112784 q = 1) (hb : d141393 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112784, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112784, d141393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112785 q = 1) (hb : d141394 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112785, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112785, d141394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112786 q = 1) (hb : d141395 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112786, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112786, d141395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112787 q = 1) (hb : d141396 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112787, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112787, d141396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112810 q = 1) (hb : d141419 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112810, d141419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112810, d141419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26010 (p : Pattern) (ha : d112813 p = 1) (hb : d141422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112692 q = 1) (hb : d141305 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25989 q ha hb
    | true =>
      simp only [d112692, d141305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112693 q = 1) (hb : d141306 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112693, d141306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112791 q = 1) (hb : d141400 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112791, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112791, d141400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112792 q = 1) (hb : d141401 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112792, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112792, d141401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112793 q = 1) (hb : d141402 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112793, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112793, d141402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112813 q = 1) (hb : d141422 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112813, d141422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112813, d141422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26011 (p : Pattern) (ha : d112819 p = 1) (hb : d141428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112766 q = 1) (hb : d141379 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112766, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26001 q ha hb
    | true =>
      simp only [d112766, d141379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28 q hb ha
  have h2 (q : Pattern) (ha : d112767 q = 1) (hb : d141380 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112767, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112767, d141380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112768 q = 1) (hb : d141381 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112768, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112768, d141381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112769 q = 1) (hb : d141382 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112769, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112769, d141382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112773 q = 1) (hb : d141386 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112773, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26002 q ha hb
    | true =>
      simp only [d112773, d141386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29 q hb ha
  have h6 (q : Pattern) (ha : d112774 q = 1) (hb : d141387 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112774, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112774, d141387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112775 q = 1) (hb : d141388 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112775, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112775, d141388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112789 q = 1) (hb : d141398 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112789, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26004 q ha hb
    | true =>
      simp only [d112789, d141398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112698 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112790 q = 1) (hb : d141399 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112790, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112790, d141399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112795 q = 1) (hb : d141404 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112795, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26005 q ha hb
    | true =>
      simp only [d112795, d141404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112796 q = 1) (hb : d141405 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112796, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112796, d141405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112797 q = 1) (hb : d141406 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112797, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112797, d141406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112798 q = 1) (hb : d141407 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112798, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112798, d141407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112799 q = 1) (hb : d141408 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112799, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112799, d141408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112802 q = 1) (hb : d141411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112802, d141411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26007 q ha hb
    | true =>
      simp only [d112802, d141411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro32 q hb ha
  have h17 (q : Pattern) (ha : d112803 q = 1) (hb : d141412 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112803, d141412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112803, d141412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112804 q = 1) (hb : d141413 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112804, d141413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112804, d141413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d112805 q = 1) (hb : d141414 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112805, d141414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112805, d141414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d112807 q = 1) (hb : d141416 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112807, d141416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26008 q ha hb
    | true =>
      simp only [d112807, d141416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro33 q hb ha
  have h21 (q : Pattern) (ha : d112808 q = 1) (hb : d141417 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112808, d141417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112808, d141417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d112809 q = 1) (hb : d141418 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112809, d141418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d112809, d141418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112811 q = 1) (hb : d141420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112811, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26009 q ha hb
    | true =>
      simp only [d112811, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25992 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112812 q = 1) (hb : d141421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d112812, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d112814 q = 1) (hb : d141423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112814, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26010 q ha hb
    | true =>
      simp only [d112814, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d112815 q = 1) (hb : d141424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112815, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d112815, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d112816 q = 1) (hb : d141425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112816, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d112817 q = 1) (hb : d141426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112817, d141426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d112817, d141426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112818 q = 1) (hb : d141427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112818, d141427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112818, d141427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112819 q = 1) (hb : d141428 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112819, d141428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112819, d141428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26012 (p : Pattern) (ha : d112821 p = 1) (hb : d141430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112698 q = 1) (hb : d141311 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25990 q ha hb
    | true =>
      simp only [d112698, d141311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h2 (q : Pattern) (ha : d112749 q = 1) (hb : d141362 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112749, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112749, d141362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112750 q = 1) (hb : d141363 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112750, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112750, d141363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112751 q = 1) (hb : d141364 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112751, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112751, d141364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112752 q = 1) (hb : d141365 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112752, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112752, d141365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d43 q = 1) (hb : d51895 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q ha hb
    | true =>
      simp only [d43, d51895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d100 q = 1) (hb : d51952 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d100, d51952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d101 q = 1) (hb : d51953 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d101, d51953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d102 q = 1) (hb : d51954 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d102, d51954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d103 q = 1) (hb : d51955 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d103, d51955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112821 q = 1) (hb : d141430 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112821, d141430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112821, d141430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro26013 (p : Pattern) (ha : d112828 p = 1) (hb : d141437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112811 q = 1) (hb : d141420 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112811, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26009 q ha hb
    | true =>
      simp only [d112811, d141420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25992 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112812 q = 1) (hb : d141421 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112812, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112812, d141421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112814 q = 1) (hb : d141423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112814, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26010 q ha hb
    | true =>
      simp only [d112814, d141423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112815 q = 1) (hb : d141424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112815, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112815, d141424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112816 q = 1) (hb : d141425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112816, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112816, d141425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112826 q = 1) (hb : d141435 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112826, d141435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112826, d141435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112827 q = 1) (hb : d141436 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112827, d141436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112827, d141436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112828 q = 1) (hb : d141437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112828, d141437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112828, d141437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26014 (p : Pattern) (ha : d112840 p = 1) (hb : d141445 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112835 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112835, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18547 q hb ha
    | true =>
      simp only [d112835, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112836 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112836, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112836, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112837 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112837, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112837, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75841 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
    | true =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75842 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75843 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112838 q = 1) (hb : d141443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112838, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112838, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d72 q = 1) (hb : d51924 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10 q ha hb
    | true =>
      simp only [d72, d51924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d73 q = 1) (hb : d51925 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d73, d51925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d74 q = 1) (hb : d51926 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d74, d51926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112723 q = 1) (hb : d141336 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112723, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112723, d141336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112839 q = 1) (hb : d141444 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112839, d141444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112839, d141444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112840 q = 1) (hb : d141445 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112840, d141445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d112840, d141445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h15 p ha hb
theorem andIntro26015 (p : Pattern) (ha : d112846 p = 1) (hb : d141451 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112841 q = 1) (hb : d141446 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112841, d141446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26014 q ha hb
    | true =>
      simp only [d112841, d141446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112842 q = 1) (hb : d141447 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112842, d141447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112842, d141447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112726 q = 1) (hb : d141339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112726, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25995 q ha hb
    | true =>
      simp only [d112726, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112727 q = 1) (hb : d141340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112727, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112727, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112843 q = 1) (hb : d141448 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112843, d141448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112843, d141448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112844 q = 1) (hb : d141449 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112844, d141449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112844, d141449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112845 q = 1) (hb : d141450 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112845, d141450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112845, d141450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112846 q = 1) (hb : d141451 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112846, d141451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112846, d141451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26016 (p : Pattern) (ha : d112852 p = 1) (hb : d141457 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112726 q = 1) (hb : d141339 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112726, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25995 q ha hb
    | true =>
      simp only [d112726, d141339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112727 q = 1) (hb : d141340 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112727, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112727, d141340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112849 q = 1) (hb : d141454 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112849, d141454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112849, d141454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112850 q = 1) (hb : d141455 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112850, d141455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112850, d141455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112851 q = 1) (hb : d141456 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112851, d141456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112851, d141456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112852 q = 1) (hb : d141457 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112852, d141457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112852, d141457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26017 (p : Pattern) (ha : d112858 p = 1) (hb : d141463 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112847 q = 1) (hb : d141452 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112847, d141452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26015 q ha hb
    | true =>
      simp only [d112847, d141452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25996 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112732 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112848 q = 1) (hb : d141453 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112848, d141453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112848, d141453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112853 q = 1) (hb : d141458 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112853, d141458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26016 q ha hb
    | true =>
      simp only [d112853, d141458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112854 q = 1) (hb : d141459 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112854, d141459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112854, d141459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112855 q = 1) (hb : d141460 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112855, d141460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112855, d141460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112856 q = 1) (hb : d141461 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112856, d141461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112856, d141461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112857 q = 1) (hb : d141462 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112857, d141462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112857, d141462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112858 q = 1) (hb : d141463 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112858, d141463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112858, d141463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26018 (p : Pattern) (ha : d112864 p = 1) (hb : d141469 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112754 q = 1) (hb : d141367 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112754, d141367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112754, d141367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25999 q ha hb
  have h2 (q : Pattern) (ha : d112755 q = 1) (hb : d141368 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112755, d141368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112755, d141368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112761 q = 1) (hb : d141374 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112761, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25999 q ha hb
    | true =>
      simp only [d112761, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26000 q ha hb
  have h4 (q : Pattern) (ha : d112762 q = 1) (hb : d141375 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112762, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112762, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112763 q = 1) (hb : d141376 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112763, d141376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112763, d141376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112820 q = 1) (hb : d141429 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112820, d141429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26006 q ha hb
    | true =>
      simp only [d112820, d141429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26011 q ha hb
  have h7 (q : Pattern) (ha : d112822 q = 1) (hb : d141431 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112822, d141431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26012 q ha hb
    | true =>
      simp only [d112822, d141431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro16 q hb ha
  have h8 (q : Pattern) (ha : d112823 q = 1) (hb : d141432 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112823, d141432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112823, d141432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112824 q = 1) (hb : d141433 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112824, d141433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112824, d141433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112825 q = 1) (hb : d141434 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112825, d141434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112825, d141434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112829 q = 1) (hb : d141438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112829, d141438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112829, d141438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26013 q ha hb
  have h12 (q : Pattern) (ha : d407 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, d52173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro39 q ha hb
  have h13 (q : Pattern) (ha : d112830 q = 1) (hb : d141439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112830, d141439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112830, d141439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  have h14 (q : Pattern) (ha : d112831 q = 1) (hb : d141440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112831, d141440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112831, d141440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d112832 q = 1) (hb : d141441 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112832, d141441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d112832, d141441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d112833 q = 1) (hb : d141442 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112833, d141442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112833, d141442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d112859 q = 1) (hb : d141464 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112859, d141464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112859, d141464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26017 q ha hb
  have h18 (q : Pattern) (ha : d463 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, d52210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro40 q ha hb
  have h19 (q : Pattern) (ha : d112860 q = 1) (hb : d141465 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112860, d141465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112860, d141465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q hb ha
  have h20 (q : Pattern) (ha : d112861 q = 1) (hb : d141466 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112861, d141466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112861, d141466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d112862 q = 1) (hb : d141467 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112862, d141467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d112862, d141467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d112863 q = 1) (hb : d141468 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d112863, d141468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d112863, d141468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112864 q = 1) (hb : d141469 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d112864, d141469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d112864, d141469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26019 (p : Pattern) (ha : d112870 p = 1) (hb : d141475 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d96 q = 1) (hb : d51948 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d96, d51948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro14 q ha hb
  have h2 (q : Pattern) (ha : d97 q = 1) (hb : d51949 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d97, d51949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d98 q = 1) (hb : d51950 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d98, d51950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d99 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d99, d51951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112744 q = 1) (hb : d141357 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112744, d141357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112744, d141357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25998 q ha hb
  have h6 (q : Pattern) (ha : d112745 q = 1) (hb : d141358 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112745, d141358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112745, d141358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112746 q = 1) (hb : d141359 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112746, d141359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112746, d141359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112747 q = 1) (hb : d141360 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112747, d141360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112747, d141360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112748 q = 1) (hb : d141361 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112748, d141361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d112748, d141361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112865 q = 1) (hb : d141470 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d112865, d141470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112865, d141470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26018 q ha hb
  have h11 (q : Pattern) (ha : d112866 q = 1) (hb : d141471 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d112866, d141471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112866, d141471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112867 q = 1) (hb : d141472 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d112867, d141472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112867, d141472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112868 q = 1) (hb : d141473 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d112868, d141473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112868, d141473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112869 q = 1) (hb : d141474 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d112869, d141474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112869, d141474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112870 q = 1) (hb : d141475 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d112870, d141475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112870, d141475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26020 (p : Pattern) (ha : d112872 p = 1) (hb : d141477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d68914 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112777 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112777, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18535 q hb ha
    | true =>
      simp only [d112777, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112778 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112778, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112778, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112779 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112779, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112779, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d68915 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
    | true =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d68916 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d68917 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112780 q = 1) (hb : d141389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112780, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112780, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d68918 q = 1) (hb : d88341 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d68918, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d68918, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d112871 q = 1) (hb : d141476 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112871, d141476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112871, d141476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d112872 q = 1) (hb : d141477 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112872, d141477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112872, d141477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26021 (p : Pattern) (ha : d112876 p = 1) (hb : d141481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d68915 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
    | true =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d68916 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d68917 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d68918 q = 1) (hb : d88341 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d68918, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d68918, d88341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112875 q = 1) (hb : d141480 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112875, d141480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112875, d141480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112876 q = 1) (hb : d141481 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112876, d141481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112876, d141481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26022 (p : Pattern) (ha : d112882 p = 1) (hb : d141487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d141485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112881 q = 1) (hb : d141486 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112881, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112881, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112882 q = 1) (hb : d141487 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112882, d141487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112882, d141487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26023 (p : Pattern) (ha : d112886 p = 1) (hb : d141491 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112883 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112884 q = 1) (hb : d141489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112884, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112884, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112885 q = 1) (hb : d141490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112885, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112885, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112886 q = 1) (hb : d141491 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112886, d141491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112886, d141491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26024 (p : Pattern) (ha : d112892 p = 1) (hb : d141497 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26022 q ha hb
    | true =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26023 q ha hb
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112892 q = 1) (hb : d141497 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112892, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112892, d141497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26025 (p : Pattern) (ha : d112895 p = 1) (hb : d141500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d141485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112881 q = 1) (hb : d141486 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112881, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112881, d141486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112895 q = 1) (hb : d141500 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112895, d141500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112895, d141500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26026 (p : Pattern) (ha : d112896 p = 1) (hb : d141501 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112883 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112884 q = 1) (hb : d141489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112884, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112884, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112885 q = 1) (hb : d141490 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112885, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112885, d141490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112896 q = 1) (hb : d141501 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112896, d141501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112896, d141501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26027 (p : Pattern) (ha : d112902 p = 1) (hb : d141507 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26022 q ha hb
    | true =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26023 q ha hb
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112897 q = 1) (hb : d141502 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112897, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26025 q ha hb
    | true =>
      simp only [d112897, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26026 q ha hb
  have h7 (q : Pattern) (ha : d112898 q = 1) (hb : d141503 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112898, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112898, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112899 q = 1) (hb : d141504 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112899, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112899, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112900 q = 1) (hb : d141505 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112900, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112900, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112901 q = 1) (hb : d141506 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112901, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112901, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112902 q = 1) (hb : d141507 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112902, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112902, d141507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26028 (p : Pattern) (ha : d112907 p = 1) (hb : d141512 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d141485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112906 q = 1) (hb : d141511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112906, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112906, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112907 q = 1) (hb : d141512 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112907, d141512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112907, d141512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26029 (p : Pattern) (ha : d112909 p = 1) (hb : d141514 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112883 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112884 q = 1) (hb : d141489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112884, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112884, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112908 q = 1) (hb : d141513 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112908, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112908, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112909 q = 1) (hb : d141514 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112909, d141514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112909, d141514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26030 (p : Pattern) (ha : d112916 p = 1) (hb : d141521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112914 q = 1) (hb : d141519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112914, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112914, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112915 q = 1) (hb : d141520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112915, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112915, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112916 q = 1) (hb : d141521 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112916, d141521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112916, d141521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26031 (p : Pattern) (ha : d112919 p = 1) (hb : d141524 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112883 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112917 q = 1) (hb : d141522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112917, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112917, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112918 q = 1) (hb : d141523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112918, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112918, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112919 q = 1) (hb : d141524 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112919, d141524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112919, d141524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26032 (p : Pattern) (ha : d112936 p = 1) (hb : d141530 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112776 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112924 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112924, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18571 q hb ha
    | true =>
      simp only [d112924, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112925 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112925, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112925, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112926 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112926, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112926, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d112930 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d112931 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112931, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18535 q hb ha
    | true =>
      simp only [d112931, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d112932 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112932, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112932, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112933 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112933, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112933, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112934 q = 1) (hb : d141528 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112934, d141528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112934, d141528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d68914 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d112777 q = 1) (hb : d114306 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112777, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18535 q hb ha
    | true =>
      simp only [d112777, d114306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d112778 q = 1) (hb : d114307 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112778, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112778, d114307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112779 q = 1) (hb : d114308 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112779, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112779, d114308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51882 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d68915 q = 1) (hb : d88338 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7917 q hb ha
    | true =>
      simp only [d68915, d88338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d68916 q = 1) (hb : d88339 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68916, d88339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d68917 q = 1) (hb : d88340 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d68917, d88340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112780 q = 1) (hb : d141389 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112780, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112780, d141389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d112935 q = 1) (hb : d141529 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d112935, d141529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d112935, d141529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d112936 q = 1) (hb : d141530 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d112936, d141530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112936, d141530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26033 (p : Pattern) (ha : d112942 p = 1) (hb : d141536 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112937 q = 1) (hb : d141531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112937, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26032 q ha hb
    | true =>
      simp only [d112937, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112938 q = 1) (hb : d141532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112938, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112938, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112939 q = 1) (hb : d141533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112939, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112939, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112940 q = 1) (hb : d141534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112940, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112940, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112941 q = 1) (hb : d141535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112941, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112941, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112942 q = 1) (hb : d141536 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112942, d141536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112942, d141536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26034 (p : Pattern) (ha : d112948 p = 1) (hb : d141542 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112945 q = 1) (hb : d141539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112945, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112945, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112946 q = 1) (hb : d141540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112946, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112946, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112947 q = 1) (hb : d141541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112947, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112947, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112948 q = 1) (hb : d141542 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112948, d141542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112948, d141542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26035 (p : Pattern) (ha : d112954 p = 1) (hb : d141548 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112910 q = 1) (hb : d141515 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112910, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26028 q ha hb
    | true =>
      simp only [d112910, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26029 q ha hb
  have h2 (q : Pattern) (ha : d112911 q = 1) (hb : d141516 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112911, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112911, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112912 q = 1) (hb : d141517 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112912, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112912, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112913 q = 1) (hb : d141518 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112913, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112913, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112920 q = 1) (hb : d141525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112920, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26030 q ha hb
    | true =>
      simp only [d112920, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26031 q ha hb
  have h6 (q : Pattern) (ha : d112921 q = 1) (hb : d141526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112921, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112921, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112922 q = 1) (hb : d141527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112922, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112922, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112943 q = 1) (hb : d141537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112943, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26033 q ha hb
    | true =>
      simp only [d112943, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26022 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112944 q = 1) (hb : d141538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112944, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112949 q = 1) (hb : d141543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112949, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26034 q ha hb
    | true =>
      simp only [d112949, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112950 q = 1) (hb : d141544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112950, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112950, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112951 q = 1) (hb : d141545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112951, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112952 q = 1) (hb : d141546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112952, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112953 q = 1) (hb : d141547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112953, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112954 q = 1) (hb : d141548 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112954, d141548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112954, d141548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26036 (p : Pattern) (ha : d112955 p = 1) (hb : d141549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112880 q = 1) (hb : d141485 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112880, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112880, d141485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112906 q = 1) (hb : d141511 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112906, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112906, d141511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112955 q = 1) (hb : d141549 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112955, d141549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112955, d141549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26037 (p : Pattern) (ha : d112956 p = 1) (hb : d141550 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112883 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112884 q = 1) (hb : d141489 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112884, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112884, d141489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112908 q = 1) (hb : d141513 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112908, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112908, d141513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112956 q = 1) (hb : d141550 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112956, d141550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112956, d141550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26038 (p : Pattern) (ha : d112961 p = 1) (hb : d141555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112879 q = 1) (hb : d141484 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112879, d141484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112914 q = 1) (hb : d141519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112914, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112914, d141519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112915 q = 1) (hb : d141520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112915, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112915, d141520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112961 q = 1) (hb : d141555 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112961, d141555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112961, d141555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26039 (p : Pattern) (ha : d112962 p = 1) (hb : d141556 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112877 q = 1) (hb : d141482 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26021 q ha hb
    | true =>
      simp only [d112877, d141482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112878 q = 1) (hb : d141483 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112878, d141483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112883 q = 1) (hb : d141488 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112883, d141488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112917 q = 1) (hb : d141522 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112917, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112917, d141522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112918 q = 1) (hb : d141523 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112918, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112918, d141523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112962 q = 1) (hb : d141556 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112962, d141556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112962, d141556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26040 (p : Pattern) (ha : d112966 p = 1) (hb : d141560 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112937 q = 1) (hb : d141531 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112937, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26032 q ha hb
    | true =>
      simp only [d112937, d141531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112938 q = 1) (hb : d141532 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112938, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112938, d141532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112939 q = 1) (hb : d141533 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112939, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112939, d141533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112940 q = 1) (hb : d141534 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112940, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112940, d141534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112941 q = 1) (hb : d141535 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112941, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112941, d141535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112966 q = 1) (hb : d141560 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112966, d141560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112966, d141560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26041 (p : Pattern) (ha : d112969 p = 1) (hb : d141563 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112873 q = 1) (hb : d141478 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26020 q ha hb
    | true =>
      simp only [d112873, d141478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112874 q = 1) (hb : d141479 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112874, d141479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112945 q = 1) (hb : d141539 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d112945, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112945, d141539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112946 q = 1) (hb : d141540 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d112946, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112946, d141540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112947 q = 1) (hb : d141541 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d112947, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112947, d141541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112969 q = 1) (hb : d141563 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d112969, d141563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112969, d141563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26042 (p : Pattern) (ha : d112975 p = 1) (hb : d141569 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112910 q = 1) (hb : d141515 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112910, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26028 q ha hb
    | true =>
      simp only [d112910, d141515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26029 q ha hb
  have h2 (q : Pattern) (ha : d112911 q = 1) (hb : d141516 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112911, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112911, d141516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112912 q = 1) (hb : d141517 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112912, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112912, d141517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112913 q = 1) (hb : d141518 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112913, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112913, d141518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112920 q = 1) (hb : d141525 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112920, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26030 q ha hb
    | true =>
      simp only [d112920, d141525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26031 q ha hb
  have h6 (q : Pattern) (ha : d112921 q = 1) (hb : d141526 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112921, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112921, d141526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112922 q = 1) (hb : d141527 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112922, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112922, d141527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d112943 q = 1) (hb : d141537 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112943, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26033 q ha hb
    | true =>
      simp only [d112943, d141537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26022 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d112887 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d112944 q = 1) (hb : d141538 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112944, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112944, d141538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d112949 q = 1) (hb : d141543 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112949, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26034 q ha hb
    | true =>
      simp only [d112949, d141543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d112950 q = 1) (hb : d141544 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112950, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112950, d141544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d112951 q = 1) (hb : d141545 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112951, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d112951, d141545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d112952 q = 1) (hb : d141546 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112952, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112952, d141546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d112953 q = 1) (hb : d141547 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112953, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112953, d141547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d112957 q = 1) (hb : d141551 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112957, d141551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26036 q ha hb
    | true =>
      simp only [d112957, d141551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26037 q ha hb
  have h17 (q : Pattern) (ha : d112958 q = 1) (hb : d141552 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112958, d141552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112958, d141552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112959 q = 1) (hb : d141553 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112959, d141553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d112959, d141553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d112960 q = 1) (hb : d141554 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112960, d141554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112960, d141554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d112963 q = 1) (hb : d141557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112963, d141557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26038 q ha hb
    | true =>
      simp only [d112963, d141557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26039 q ha hb
  have h21 (q : Pattern) (ha : d112964 q = 1) (hb : d141558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112964, d141558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112964, d141558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d112965 q = 1) (hb : d141559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112965, d141559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d112965, d141559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d112967 q = 1) (hb : d141561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112967, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26040 q ha hb
    | true =>
      simp only [d112967, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26025 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d112897 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d112968 q = 1) (hb : d141562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d112968, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d112970 q = 1) (hb : d141564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112970, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26041 q ha hb
    | true =>
      simp only [d112970, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d112971 q = 1) (hb : d141565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112971, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d112971, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d112972 q = 1) (hb : d141566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d112972, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d112973 q = 1) (hb : d141567 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112973, d141567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d112973, d141567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d112974 q = 1) (hb : d141568 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112974, d141568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d112974, d141568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d112975 q = 1) (hb : d141569 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112975, d141569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d112975, d141569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26043 (p : Pattern) (ha : d112982 p = 1) (hb : d141576 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112887 q = 1) (hb : d141492 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26022 q ha hb
    | true =>
      simp only [d112887, d141492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26023 q ha hb
  have h2 (q : Pattern) (ha : d112888 q = 1) (hb : d141493 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112888, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112888, d141493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112889 q = 1) (hb : d141494 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112889, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112889, d141494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112890 q = 1) (hb : d141495 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112890, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112890, d141495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112891 q = 1) (hb : d141496 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112891, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112891, d141496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112977 q = 1) (hb : d141571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112977, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26023 q ha hb
    | true =>
      simp only [d112977, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112978 q = 1) (hb : d141572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112978, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112978, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112979 q = 1) (hb : d141573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112979, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112979, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112980 q = 1) (hb : d141574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112980, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112980, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112981 q = 1) (hb : d141575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112981, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112981, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112982 q = 1) (hb : d141576 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112982, d141576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112982, d141576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26044 (p : Pattern) (ha : d112988 p = 1) (hb : d141582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112977 q = 1) (hb : d141571 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112977, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26023 q ha hb
    | true =>
      simp only [d112977, d141571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112978 q = 1) (hb : d141572 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112978, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112978, d141572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112979 q = 1) (hb : d141573 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112979, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112979, d141573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112980 q = 1) (hb : d141574 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112980, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112980, d141574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112981 q = 1) (hb : d141575 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112981, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112981, d141575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112983 q = 1) (hb : d141577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112983, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26026 q ha hb
    | true =>
      simp only [d112983, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d112984 q = 1) (hb : d141578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112984, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112984, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112985 q = 1) (hb : d141579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112985, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d112985, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d112986 q = 1) (hb : d141580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112986, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112986, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d112987 q = 1) (hb : d141581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112987, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112987, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112988 q = 1) (hb : d141582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112988, d141582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112988, d141582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26045 (p : Pattern) (ha : d112995 p = 1) (hb : d141589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112967 q = 1) (hb : d141561 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112967, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26040 q ha hb
    | true =>
      simp only [d112967, d141561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26025 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d112897 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d112968 q = 1) (hb : d141562 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112968, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112968, d141562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d112970 q = 1) (hb : d141564 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112970, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26041 q ha hb
    | true =>
      simp only [d112970, d141564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112971 q = 1) (hb : d141565 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112971, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112971, d141565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d112972 q = 1) (hb : d141566 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112972, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112972, d141566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d112993 q = 1) (hb : d141587 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112993, d141587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112993, d141587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d112994 q = 1) (hb : d141588 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112994, d141588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112994, d141588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112995 q = 1) (hb : d141589 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112995, d141589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112995, d141589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26046 (p : Pattern) (ha : d112997 p = 1) (hb : d141591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112983 q = 1) (hb : d141577 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d112983, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26026 q ha hb
    | true =>
      simp only [d112983, d141577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d112984 q = 1) (hb : d141578 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d112984, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112984, d141578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d112985 q = 1) (hb : d141579 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d112985, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112985, d141579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d112986 q = 1) (hb : d141580 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d112986, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112986, d141580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d112987 q = 1) (hb : d141581 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d112987, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112987, d141581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112997 q = 1) (hb : d141591 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d112997, d141591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112997, d141591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26047 (p : Pattern) (ha : d113018 p = 1) (hb : d141599 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112834 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113004 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113004, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18585 q hb ha
    | true =>
      simp only [d113004, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113005 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113005, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113005, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113006 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113006, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113006, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113012 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113013 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113013, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18547 q hb ha
    | true =>
      simp only [d113013, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113014 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113014, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113014, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113015 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113015, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113015, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113016 q = 1) (hb : d141597 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113016, d141597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113016, d141597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d75840 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d112835 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112835, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18547 q hb ha
    | true =>
      simp only [d112835, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d112836 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112836, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112836, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d112837 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112837, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112837, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75841 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
    | true =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75842 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75843 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d112838 q = 1) (hb : d141443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112838, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d112838, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113017 q = 1) (hb : d141598 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113017, d141598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113017, d141598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113018 q = 1) (hb : d141599 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113018, d141599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113018, d141599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26048 (p : Pattern) (ha : d113022 p = 1) (hb : d141603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75840 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d112835 q = 1) (hb : d114363 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d112835, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18547 q hb ha
    | true =>
      simp only [d112835, d114363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d112836 q = 1) (hb : d114364 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d112836, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112836, d114364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d112837 q = 1) (hb : d114365 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d112837, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112837, d114365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75841 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
    | true =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75842 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75843 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112838 q = 1) (hb : d141443 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d112838, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d112838, d141443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75844 q = 1) (hb : d88405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75844, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75844, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113021 q = 1) (hb : d141602 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113021, d141602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113021, d141602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113022 q = 1) (hb : d141603 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113022, d141603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113022, d141603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26049 (p : Pattern) (ha : d113028 p = 1) (hb : d141609 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113019 q = 1) (hb : d141600 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113019, d141600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26047 q ha hb
    | true =>
      simp only [d113019, d141600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113020 q = 1) (hb : d141601 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113020, d141601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113020, d141601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113023 q = 1) (hb : d141604 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26048 q ha hb
    | true =>
      simp only [d113023, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113024 q = 1) (hb : d141605 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113025 q = 1) (hb : d141606 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113025, d141606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113025, d141606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113026 q = 1) (hb : d141607 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113026, d141607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113026, d141607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113027 q = 1) (hb : d141608 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113027, d141608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113027, d141608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113028 q = 1) (hb : d141609 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113028, d141609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113028, d141609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26050 (p : Pattern) (ha : d113030 p = 1) (hb : d141611 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75841 q = 1) (hb : d88402 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10860 q hb ha
    | true =>
      simp only [d75841, d88402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d75842 q = 1) (hb : d88403 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75842, d88403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75843 q = 1) (hb : d88404 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75843, d88404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75844 q = 1) (hb : d88405 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75844, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75844, d88405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113029 q = 1) (hb : d141610 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113029, d141610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113029, d141610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113030 q = 1) (hb : d141611 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113030, d141611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113030, d141611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26051 (p : Pattern) (ha : d113036 p = 1) (hb : d141617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113023 q = 1) (hb : d141604 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26048 q ha hb
    | true =>
      simp only [d113023, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113024 q = 1) (hb : d141605 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113031 q = 1) (hb : d141612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113031, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26050 q ha hb
    | true =>
      simp only [d113031, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113032 q = 1) (hb : d141613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113032, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113032, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113033 q = 1) (hb : d141614 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113033, d141614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113033, d141614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113034 q = 1) (hb : d141615 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113034, d141615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113034, d141615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113035 q = 1) (hb : d141616 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113035, d141616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113035, d141616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113036 q = 1) (hb : d141617 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113036, d141617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113036, d141617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26052 (p : Pattern) (ha : d113047 p = 1) (hb : d141623 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113023 q = 1) (hb : d141604 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113023, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26048 q ha hb
    | true =>
      simp only [d113023, d141604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113024 q = 1) (hb : d141605 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113024, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113024, d141605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113044 q = 1) (hb : d141620 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113044, d141620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113044, d141620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113045 q = 1) (hb : d141621 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113045, d141621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113045, d141621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113046 q = 1) (hb : d141622 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113046, d141622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113046, d141622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113047 q = 1) (hb : d141623 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113047, d141623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113047, d141623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26053 (p : Pattern) (ha : d113053 p = 1) (hb : d141629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113037 q = 1) (hb : d141618 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113037, d141618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26049 q ha hb
    | true =>
      simp only [d113037, d141618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26051 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113042 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113043 q = 1) (hb : d141619 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113043, d141619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113043, d141619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113048 q = 1) (hb : d141624 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113048, d141624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26052 q ha hb
    | true =>
      simp only [d113048, d141624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113049 q = 1) (hb : d141625 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113049, d141625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113049, d141625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113050 q = 1) (hb : d141626 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113050, d141626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113050, d141626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113051 q = 1) (hb : d141627 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113051, d141627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113051, d141627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113052 q = 1) (hb : d141628 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113052, d141628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113052, d141628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113053 q = 1) (hb : d141629 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113053, d141629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113053, d141629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26054 (p : Pattern) (ha : d113041 p = 1) (hb : d141634 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113031 q = 1) (hb : d141612 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113031, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26050 q ha hb
    | true =>
      simp only [d113031, d141612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113032 q = 1) (hb : d141613 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113032, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113032, d141613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113038 q = 1) (hb : d141631 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113038, d141631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113038, d141631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113039 q = 1) (hb : d141632 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113039, d141632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113039, d141632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113040 q = 1) (hb : d141633 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113040, d141633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113040, d141633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113041 q = 1) (hb : d141634 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113041, d141634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113041, d141634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26055 (p : Pattern) (ha : d113060 p = 1) (hb : d141640 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113055 q = 1) (hb : d141635 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113055, d141635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26054 q ha hb
    | true =>
      simp only [d113055, d141635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113056 q = 1) (hb : d141636 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113056, d141636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113056, d141636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113057 q = 1) (hb : d141637 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113057, d141637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113057, d141637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113058 q = 1) (hb : d141638 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113058, d141638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113058, d141638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113059 q = 1) (hb : d141639 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113059, d141639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113059, d141639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113060 q = 1) (hb : d141640 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113060, d141640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113060, d141640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26056 (p : Pattern) (ha : d113066 p = 1) (hb : d141646 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112893 q = 1) (hb : d141498 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112893, d141498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112893, d141498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26024 q ha hb
  have h2 (q : Pattern) (ha : d112894 q = 1) (hb : d141499 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112894, d141499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d112894, d141499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d112903 q = 1) (hb : d141508 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112903, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26024 q ha hb
    | true =>
      simp only [d112903, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26027 q ha hb
  have h4 (q : Pattern) (ha : d112904 q = 1) (hb : d141509 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112904, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d112904, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d112905 q = 1) (hb : d141510 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112905, d141510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d112905, d141510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d112976 q = 1) (hb : d141570 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112976, d141570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26035 q ha hb
    | true =>
      simp only [d112976, d141570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26042 q ha hb
  have h7 (q : Pattern) (ha : d112989 q = 1) (hb : d141583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112989, d141583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26043 q ha hb
    | true =>
      simp only [d112989, d141583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26044 q ha hb
  have h8 (q : Pattern) (ha : d112990 q = 1) (hb : d141584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112990, d141584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d112990, d141584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d112991 q = 1) (hb : d141585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d112991, d141585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d112991, d141585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d112992 q = 1) (hb : d141586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d112992, d141586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d112992, d141586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d112996 q = 1) (hb : d141590 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112996, d141590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112996, d141590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26045 q ha hb
  have h12 (q : Pattern) (ha : d112998 q = 1) (hb : d141592 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112998, d141592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d112998, d141592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26046 q ha hb
  have h13 (q : Pattern) (ha : d112999 q = 1) (hb : d141593 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d112999, d141593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d112999, d141593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113000 q = 1) (hb : d141594 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113000, d141594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113000, d141594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113001 q = 1) (hb : d141595 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113001, d141595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113001, d141595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113002 q = 1) (hb : d141596 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113002, d141596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113002, d141596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113054 q = 1) (hb : d141630 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113054, d141630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113054, d141630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26053 q ha hb
  have h18 (q : Pattern) (ha : d113061 q = 1) (hb : d141641 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113061, d141641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113061, d141641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26055 q ha hb
  have h19 (q : Pattern) (ha : d113062 q = 1) (hb : d141642 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113062, d141642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113062, d141642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113063 q = 1) (hb : d141643 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113063, d141643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113063, d141643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113064 q = 1) (hb : d141644 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113064, d141644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113064, d141644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113065 q = 1) (hb : d141645 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113065, d141645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113065, d141645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113066 q = 1) (hb : d141646 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113066, d141646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113066, d141646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26057 (p : Pattern) (ha : d113072 p = 1) (hb : d141652 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113067 q = 1) (hb : d141647 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113067, d141647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113067, d141647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26056 q ha hb
  have h2 (q : Pattern) (ha : d113068 q = 1) (hb : d141648 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113068, d141648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113068, d141648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113069 q = 1) (hb : d141649 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113069, d141649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113069, d141649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113070 q = 1) (hb : d141650 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113070, d141650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113070, d141650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113071 q = 1) (hb : d141651 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113071, d141651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113071, d141651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113072 q = 1) (hb : d141652 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113072, d141652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113072, d141652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26058 (p : Pattern) (ha : d113079 p = 1) (hb : d141656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69006 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113074 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113074, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18571 q hb ha
    | true =>
      simp only [d113074, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113075 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113075, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113075, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113076 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113076, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113076, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69007 q = 1) (hb : d88489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69007, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q hb ha
    | true =>
      simp only [d69007, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69008 q = 1) (hb : d88490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69008, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69008, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69009 q = 1) (hb : d88491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69009, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69009, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113077 q = 1) (hb : d141654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113077, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113077, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69010 q = 1) (hb : d88492 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69010, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69010, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113078 q = 1) (hb : d141655 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113078, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113078, d141655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113079 q = 1) (hb : d141656 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113079, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113079, d141656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26059 (p : Pattern) (ha : d113083 p = 1) (hb : d141660 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d69007 q = 1) (hb : d88489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69007, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q hb ha
    | true =>
      simp only [d69007, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d69008 q = 1) (hb : d88490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69008, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69008, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d69009 q = 1) (hb : d88491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69009, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69009, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d69010 q = 1) (hb : d88492 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69010, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d69010, d88492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113082 q = 1) (hb : d141659 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113082, d141659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113082, d141659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113083 q = 1) (hb : d141660 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113083, d141660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113083, d141660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26060 (p : Pattern) (ha : d113089 p = 1) (hb : d141666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d141664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113088 q = 1) (hb : d141665 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113088, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113088, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113089 q = 1) (hb : d141666 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113089, d141666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113089, d141666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26061 (p : Pattern) (ha : d113093 p = 1) (hb : d141670 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113090 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113091 q = 1) (hb : d141668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113091, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113091, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113092 q = 1) (hb : d141669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113092, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113092, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113093 q = 1) (hb : d141670 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113093, d141670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113093, d141670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26062 (p : Pattern) (ha : d113099 p = 1) (hb : d141676 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26060 q ha hb
    | true =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26061 q ha hb
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113099 q = 1) (hb : d141676 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113099, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113099, d141676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26063 (p : Pattern) (ha : d113102 p = 1) (hb : d141679 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d141664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113088 q = 1) (hb : d141665 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113088, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113088, d141665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113102 q = 1) (hb : d141679 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113102, d141679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113102, d141679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26064 (p : Pattern) (ha : d113103 p = 1) (hb : d141680 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113090 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113091 q = 1) (hb : d141668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113091, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113091, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113092 q = 1) (hb : d141669 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113092, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113092, d141669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113103 q = 1) (hb : d141680 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113103, d141680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113103, d141680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26065 (p : Pattern) (ha : d113109 p = 1) (hb : d141686 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26060 q ha hb
    | true =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26061 q ha hb
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113104 q = 1) (hb : d141681 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113104, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26063 q ha hb
    | true =>
      simp only [d113104, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26064 q ha hb
  have h7 (q : Pattern) (ha : d113105 q = 1) (hb : d141682 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113105, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113105, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113106 q = 1) (hb : d141683 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113106, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113106, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113107 q = 1) (hb : d141684 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113107, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113107, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113108 q = 1) (hb : d141685 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113108, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113108, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113109 q = 1) (hb : d141686 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113109, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113109, d141686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26066 (p : Pattern) (ha : d113114 p = 1) (hb : d141691 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d141664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113113 q = 1) (hb : d141690 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113113, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113113, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113114 q = 1) (hb : d141691 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113114, d141691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113114, d141691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26067 (p : Pattern) (ha : d113116 p = 1) (hb : d141693 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113090 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113091 q = 1) (hb : d141668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113091, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113091, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113115 q = 1) (hb : d141692 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113115, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113115, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113116 q = 1) (hb : d141693 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113116, d141693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113116, d141693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26068 (p : Pattern) (ha : d113123 p = 1) (hb : d141700 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113121 q = 1) (hb : d141698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113121, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113121, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113122 q = 1) (hb : d141699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113122, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113122, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113123 q = 1) (hb : d141700 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113123, d141700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113123, d141700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26069 (p : Pattern) (ha : d113126 p = 1) (hb : d141703 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113090 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113124 q = 1) (hb : d141701 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113124, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113124, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113125 q = 1) (hb : d141702 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113125, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113125, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113126 q = 1) (hb : d141703 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113126, d141703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113126, d141703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26070 (p : Pattern) (ha : d113143 p = 1) (hb : d141712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112923 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113131 q = 1) (hb : d141707 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113131, d141707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18611 q hb ha
    | true =>
      simp only [d113131, d141707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113132 q = 1) (hb : d141708 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113132, d141708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113132, d141708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113133 q = 1) (hb : d141709 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113133, d141709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113133, d141709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113137 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113138 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113138, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18571 q hb ha
    | true =>
      simp only [d113138, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113139 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113139, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113139, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113140 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113140, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113140, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113141 q = 1) (hb : d141710 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113141, d141710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113141, d141710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69006 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d113074 q = 1) (hb : d114443 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113074, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18571 q hb ha
    | true =>
      simp only [d113074, d114443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d113075 q = 1) (hb : d114444 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113075, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113075, d114444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113076 q = 1) (hb : d114445 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113076, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113076, d114445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52439 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69007 q = 1) (hb : d88489 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69007, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7931 q hb ha
    | true =>
      simp only [d69007, d88489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d69008 q = 1) (hb : d88490 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69008, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69008, d88490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69009 q = 1) (hb : d88491 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69009, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69009, d88491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113077 q = 1) (hb : d141654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113077, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113077, d141654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113142 q = 1) (hb : d141711 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113142, d141711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113142, d141711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113143 q = 1) (hb : d141712 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113143, d141712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113143, d141712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26071 (p : Pattern) (ha : d113149 p = 1) (hb : d141718 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113144 q = 1) (hb : d141713 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113144, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26070 q ha hb
    | true =>
      simp only [d113144, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113145 q = 1) (hb : d141714 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113145, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113145, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113146 q = 1) (hb : d141715 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113146, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113146, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113147 q = 1) (hb : d141716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113147, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113147, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113148 q = 1) (hb : d141717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113148, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113148, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113149 q = 1) (hb : d141718 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113149, d141718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113149, d141718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26072 (p : Pattern) (ha : d113155 p = 1) (hb : d141724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113152 q = 1) (hb : d141721 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113152, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113152, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113153 q = 1) (hb : d141722 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113153, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113153, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113154 q = 1) (hb : d141723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113154, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113154, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113155 q = 1) (hb : d141724 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113155, d141724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113155, d141724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26073 (p : Pattern) (ha : d113161 p = 1) (hb : d141730 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113117 q = 1) (hb : d141694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113117, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26066 q ha hb
    | true =>
      simp only [d113117, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26067 q ha hb
  have h2 (q : Pattern) (ha : d113118 q = 1) (hb : d141695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113118, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113118, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113119 q = 1) (hb : d141696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113119, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113119, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113120 q = 1) (hb : d141697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113120, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113120, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113127 q = 1) (hb : d141704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113127, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26068 q ha hb
    | true =>
      simp only [d113127, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26069 q ha hb
  have h6 (q : Pattern) (ha : d113128 q = 1) (hb : d141705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113128, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113128, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113129 q = 1) (hb : d141706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113129, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113129, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113150 q = 1) (hb : d141719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113150, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26071 q ha hb
    | true =>
      simp only [d113150, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26060 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113094 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113151 q = 1) (hb : d141720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113151, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113156 q = 1) (hb : d141725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113156, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26072 q ha hb
    | true =>
      simp only [d113156, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113157 q = 1) (hb : d141726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113157, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113157, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113158 q = 1) (hb : d141727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113158, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113159 q = 1) (hb : d141728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113159, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113160 q = 1) (hb : d141729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113160, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113161 q = 1) (hb : d141730 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113161, d141730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113161, d141730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26074 (p : Pattern) (ha : d113162 p = 1) (hb : d141731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113087 q = 1) (hb : d141664 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113087, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113087, d141664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113113 q = 1) (hb : d141690 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113113, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113113, d141690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113162 q = 1) (hb : d141731 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113162, d141731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113162, d141731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26075 (p : Pattern) (ha : d113163 p = 1) (hb : d141732 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113090 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113091 q = 1) (hb : d141668 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113091, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113091, d141668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113115 q = 1) (hb : d141692 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113115, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113115, d141692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113163 q = 1) (hb : d141732 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113163, d141732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113163, d141732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26076 (p : Pattern) (ha : d113168 p = 1) (hb : d141737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113086 q = 1) (hb : d141663 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113086, d141663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113121 q = 1) (hb : d141698 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113121, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113121, d141698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113122 q = 1) (hb : d141699 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113122, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113122, d141699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113168 q = 1) (hb : d141737 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113168, d141737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113168, d141737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26077 (p : Pattern) (ha : d113169 p = 1) (hb : d141738 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113084 q = 1) (hb : d141661 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26059 q ha hb
    | true =>
      simp only [d113084, d141661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113085 q = 1) (hb : d141662 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113085, d141662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113090 q = 1) (hb : d141667 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113090, d141667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113124 q = 1) (hb : d141701 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113124, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113124, d141701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113125 q = 1) (hb : d141702 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113125, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113125, d141702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113169 q = 1) (hb : d141738 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113169, d141738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113169, d141738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26078 (p : Pattern) (ha : d113173 p = 1) (hb : d141742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113144 q = 1) (hb : d141713 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113144, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26070 q ha hb
    | true =>
      simp only [d113144, d141713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113145 q = 1) (hb : d141714 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113145, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113145, d141714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113146 q = 1) (hb : d141715 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113146, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113146, d141715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113147 q = 1) (hb : d141716 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113147, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113147, d141716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113148 q = 1) (hb : d141717 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113148, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113148, d141717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113173 q = 1) (hb : d141742 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113173, d141742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113173, d141742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26079 (p : Pattern) (ha : d113176 p = 1) (hb : d141745 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113080 q = 1) (hb : d141657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26058 q ha hb
    | true =>
      simp only [d113080, d141657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113081 q = 1) (hb : d141658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113081, d141658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113152 q = 1) (hb : d141721 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113152, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113152, d141721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113153 q = 1) (hb : d141722 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113153, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113153, d141722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113154 q = 1) (hb : d141723 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113154, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113154, d141723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113176 q = 1) (hb : d141745 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113176, d141745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113176, d141745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26080 (p : Pattern) (ha : d113182 p = 1) (hb : d141751 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113117 q = 1) (hb : d141694 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113117, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26066 q ha hb
    | true =>
      simp only [d113117, d141694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26067 q ha hb
  have h2 (q : Pattern) (ha : d113118 q = 1) (hb : d141695 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113118, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113118, d141695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113119 q = 1) (hb : d141696 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113119, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113119, d141696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113120 q = 1) (hb : d141697 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113120, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113120, d141697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113127 q = 1) (hb : d141704 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113127, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26068 q ha hb
    | true =>
      simp only [d113127, d141704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26069 q ha hb
  have h6 (q : Pattern) (ha : d113128 q = 1) (hb : d141705 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113128, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113128, d141705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113129 q = 1) (hb : d141706 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113129, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113129, d141706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113150 q = 1) (hb : d141719 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113150, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26071 q ha hb
    | true =>
      simp only [d113150, d141719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26060 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113094 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113151 q = 1) (hb : d141720 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113151, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113151, d141720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113156 q = 1) (hb : d141725 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113156, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26072 q ha hb
    | true =>
      simp only [d113156, d141725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113157 q = 1) (hb : d141726 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113157, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113157, d141726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113158 q = 1) (hb : d141727 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113158, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113158, d141727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113159 q = 1) (hb : d141728 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113159, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113159, d141728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113160 q = 1) (hb : d141729 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113160, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113160, d141729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113164 q = 1) (hb : d141733 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113164, d141733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26074 q ha hb
    | true =>
      simp only [d113164, d141733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26075 q ha hb
  have h17 (q : Pattern) (ha : d113165 q = 1) (hb : d141734 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113165, d141734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113165, d141734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113166 q = 1) (hb : d141735 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113166, d141735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113166, d141735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113167 q = 1) (hb : d141736 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113167, d141736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113167, d141736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113170 q = 1) (hb : d141739 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113170, d141739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26076 q ha hb
    | true =>
      simp only [d113170, d141739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26077 q ha hb
  have h21 (q : Pattern) (ha : d113171 q = 1) (hb : d141740 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113171, d141740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113171, d141740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113172 q = 1) (hb : d141741 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113172, d141741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113172, d141741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113174 q = 1) (hb : d141743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113174, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26078 q ha hb
    | true =>
      simp only [d113174, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26063 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113104 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113175 q = 1) (hb : d141744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113175, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113177 q = 1) (hb : d141746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113177, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26079 q ha hb
    | true =>
      simp only [d113177, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113178 q = 1) (hb : d141747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113178, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113178, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113179 q = 1) (hb : d141748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113179, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113180 q = 1) (hb : d141749 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113180, d141749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113180, d141749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113181 q = 1) (hb : d141750 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113181, d141750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113181, d141750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113182 q = 1) (hb : d141751 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113182, d141751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113182, d141751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26081 (p : Pattern) (ha : d113189 p = 1) (hb : d141758 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113094 q = 1) (hb : d141671 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26060 q ha hb
    | true =>
      simp only [d113094, d141671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26061 q ha hb
  have h2 (q : Pattern) (ha : d113095 q = 1) (hb : d141672 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113095, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113095, d141672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113096 q = 1) (hb : d141673 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113096, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113096, d141673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113097 q = 1) (hb : d141674 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113097, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113097, d141674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113098 q = 1) (hb : d141675 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113098, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113098, d141675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113184 q = 1) (hb : d141753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113184, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26061 q ha hb
    | true =>
      simp only [d113184, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113185 q = 1) (hb : d141754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113185, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113185, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113186 q = 1) (hb : d141755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113186, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113186, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113187 q = 1) (hb : d141756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113187, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113187, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113188 q = 1) (hb : d141757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113188, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113188, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113189 q = 1) (hb : d141758 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113189, d141758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113189, d141758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26082 (p : Pattern) (ha : d113195 p = 1) (hb : d141764 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113184 q = 1) (hb : d141753 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113184, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26061 q ha hb
    | true =>
      simp only [d113184, d141753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113185 q = 1) (hb : d141754 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113185, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113185, d141754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113186 q = 1) (hb : d141755 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113186, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113186, d141755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113187 q = 1) (hb : d141756 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113187, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113187, d141756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113188 q = 1) (hb : d141757 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113188, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113188, d141757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113190 q = 1) (hb : d141759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113190, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26064 q ha hb
    | true =>
      simp only [d113190, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113191 q = 1) (hb : d141760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113191, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113191, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113192 q = 1) (hb : d141761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113192, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113192, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113193 q = 1) (hb : d141762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113193, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113193, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113194 q = 1) (hb : d141763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113194, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113194, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113195 q = 1) (hb : d141764 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113195, d141764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113195, d141764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26083 (p : Pattern) (ha : d113202 p = 1) (hb : d141771 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113174 q = 1) (hb : d141743 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113174, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26078 q ha hb
    | true =>
      simp only [d113174, d141743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26063 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113104 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113175 q = 1) (hb : d141744 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113175, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113175, d141744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113177 q = 1) (hb : d141746 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113177, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26079 q ha hb
    | true =>
      simp only [d113177, d141746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113178 q = 1) (hb : d141747 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113178, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113178, d141747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113179 q = 1) (hb : d141748 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113179, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113179, d141748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113200 q = 1) (hb : d141769 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113200, d141769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113200, d141769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113201 q = 1) (hb : d141770 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113201, d141770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113201, d141770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113202 q = 1) (hb : d141771 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113202, d141771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113202, d141771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26084 (p : Pattern) (ha : d113204 p = 1) (hb : d141773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113190 q = 1) (hb : d141759 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113190, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26064 q ha hb
    | true =>
      simp only [d113190, d141759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113191 q = 1) (hb : d141760 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113191, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113191, d141760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113192 q = 1) (hb : d141761 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113192, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113192, d141761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113193 q = 1) (hb : d141762 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113193, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113193, d141762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113194 q = 1) (hb : d141763 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113194, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113194, d141763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113204 q = 1) (hb : d141773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113204, d141773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113204, d141773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26085 (p : Pattern) (ha : d113229 p = 1) (hb : d141785 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113003 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113211 q = 1) (hb : d141779 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113211, d141779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18625 q hb ha
    | true =>
      simp only [d113211, d141779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113212 q = 1) (hb : d141780 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113212, d141780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113212, d141780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113213 q = 1) (hb : d141781 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113213, d141781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113213, d141781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113219 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113220 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113220, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18585 q hb ha
    | true =>
      simp only [d113220, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113221 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113221, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113221, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113222 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113222, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113222, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113223 q = 1) (hb : d141782 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113223, d141782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113223, d141782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d75961 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d113224 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113224, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18585 q hb ha
    | true =>
      simp only [d113224, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d113225 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113225, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113225, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113226 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113226, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113226, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d75962 q = 1) (hb : d88553 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75962, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q hb ha
    | true =>
      simp only [d75962, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d75963 q = 1) (hb : d88554 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75963, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75963, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d75964 q = 1) (hb : d88555 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75964, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75964, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113227 q = 1) (hb : d141783 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113227, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113227, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113228 q = 1) (hb : d141784 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113228, d141784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113228, d141784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113229 q = 1) (hb : d141785 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113229, d141785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113229, d141785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26086 (p : Pattern) (ha : d113233 p = 1) (hb : d141789 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d75961 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113224 q = 1) (hb : d114500 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113224, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18585 q hb ha
    | true =>
      simp only [d113224, d114500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113225 q = 1) (hb : d114501 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113225, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113225, d114501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113226 q = 1) (hb : d114502 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113226, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113226, d114502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d75962 q = 1) (hb : d88553 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75962, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q hb ha
    | true =>
      simp only [d75962, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d75963 q = 1) (hb : d88554 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75963, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75963, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d75964 q = 1) (hb : d88555 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75964, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75964, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113227 q = 1) (hb : d141783 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113227, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113227, d141783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d75965 q = 1) (hb : d88556 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75965, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d75965, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113232 q = 1) (hb : d141788 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113232, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113232, d141788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113233 q = 1) (hb : d141789 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113233, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113233, d141789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26087 (p : Pattern) (ha : d113239 p = 1) (hb : d141795 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113230 q = 1) (hb : d141786 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113230, d141786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26085 q ha hb
    | true =>
      simp only [d113230, d141786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113231 q = 1) (hb : d141787 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113231, d141787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113231, d141787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113234 q = 1) (hb : d141790 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26086 q ha hb
    | true =>
      simp only [d113234, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113235 q = 1) (hb : d141791 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113236 q = 1) (hb : d141792 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113236, d141792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113236, d141792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113237 q = 1) (hb : d141793 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113237, d141793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113237, d141793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113238 q = 1) (hb : d141794 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113238, d141794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113238, d141794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113239 q = 1) (hb : d141795 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113239, d141795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113239, d141795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26088 (p : Pattern) (ha : d113241 p = 1) (hb : d141797 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52605 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d75962 q = 1) (hb : d88553 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d75962, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10873 q hb ha
    | true =>
      simp only [d75962, d88553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d75963 q = 1) (hb : d88554 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d75963, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75963, d88554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d75964 q = 1) (hb : d88555 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d75964, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d75964, d88555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d75965 q = 1) (hb : d88556 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d75965, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d75965, d88556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113240 q = 1) (hb : d141796 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113240, d141796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113240, d141796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113241 q = 1) (hb : d141797 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113241, d141797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113241, d141797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26089 (p : Pattern) (ha : d113247 p = 1) (hb : d141803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113234 q = 1) (hb : d141790 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26086 q ha hb
    | true =>
      simp only [d113234, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113235 q = 1) (hb : d141791 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113242 q = 1) (hb : d141798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113242, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26088 q ha hb
    | true =>
      simp only [d113242, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113243 q = 1) (hb : d141799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113243, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113243, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113244 q = 1) (hb : d141800 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113244, d141800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113244, d141800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113245 q = 1) (hb : d141801 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113245, d141801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113245, d141801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113246 q = 1) (hb : d141802 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113246, d141802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113246, d141802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113247 q = 1) (hb : d141803 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113247, d141803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113247, d141803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26090 (p : Pattern) (ha : d113258 p = 1) (hb : d141809 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113234 q = 1) (hb : d141790 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113234, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26086 q ha hb
    | true =>
      simp only [d113234, d141790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113235 q = 1) (hb : d141791 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113235, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113235, d141791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113255 q = 1) (hb : d141806 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113255, d141806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113255, d141806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113256 q = 1) (hb : d141807 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113256, d141807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113256, d141807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113257 q = 1) (hb : d141808 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113257, d141808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113257, d141808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113258 q = 1) (hb : d141809 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113258, d141809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113258, d141809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26091 (p : Pattern) (ha : d113264 p = 1) (hb : d141815 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113248 q = 1) (hb : d141804 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113248, d141804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26087 q ha hb
    | true =>
      simp only [d113248, d141804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26089 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113253 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113254 q = 1) (hb : d141805 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113254, d141805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113254, d141805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113259 q = 1) (hb : d141810 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113259, d141810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26090 q ha hb
    | true =>
      simp only [d113259, d141810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113260 q = 1) (hb : d141811 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113260, d141811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113260, d141811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113261 q = 1) (hb : d141812 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113261, d141812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113261, d141812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113262 q = 1) (hb : d141813 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113262, d141813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113262, d141813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113263 q = 1) (hb : d141814 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113263, d141814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113263, d141814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113264 q = 1) (hb : d141815 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113264, d141815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113264, d141815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26092 (p : Pattern) (ha : d113252 p = 1) (hb : d141820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113242 q = 1) (hb : d141798 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113242, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26088 q ha hb
    | true =>
      simp only [d113242, d141798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113243 q = 1) (hb : d141799 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113243, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113243, d141799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113249 q = 1) (hb : d141817 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113249, d141817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113249, d141817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113250 q = 1) (hb : d141818 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113250, d141818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113250, d141818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113251 q = 1) (hb : d141819 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113251, d141819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113251, d141819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113252 q = 1) (hb : d141820 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113252, d141820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113252, d141820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26093 (p : Pattern) (ha : d113271 p = 1) (hb : d141826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113266 q = 1) (hb : d141821 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113266, d141821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26092 q ha hb
    | true =>
      simp only [d113266, d141821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113267 q = 1) (hb : d141822 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113267, d141822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113267, d141822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113268 q = 1) (hb : d141823 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113268, d141823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113268, d141823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113269 q = 1) (hb : d141824 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113269, d141824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113269, d141824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113270 q = 1) (hb : d141825 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113270, d141825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113270, d141825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113271 q = 1) (hb : d141826 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113271, d141826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113271, d141826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26094 (p : Pattern) (ha : d113277 p = 1) (hb : d141832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113100 q = 1) (hb : d141677 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113100, d141677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113100, d141677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26062 q ha hb
  have h2 (q : Pattern) (ha : d113101 q = 1) (hb : d141678 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113101, d141678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113101, d141678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113110 q = 1) (hb : d141687 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113110, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26062 q ha hb
    | true =>
      simp only [d113110, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26065 q ha hb
  have h4 (q : Pattern) (ha : d113111 q = 1) (hb : d141688 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113111, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113111, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113112 q = 1) (hb : d141689 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113112, d141689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113112, d141689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113183 q = 1) (hb : d141752 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113183, d141752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26073 q ha hb
    | true =>
      simp only [d113183, d141752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26080 q ha hb
  have h7 (q : Pattern) (ha : d113196 q = 1) (hb : d141765 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113196, d141765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26081 q ha hb
    | true =>
      simp only [d113196, d141765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26082 q ha hb
  have h8 (q : Pattern) (ha : d113197 q = 1) (hb : d141766 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113197, d141766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113197, d141766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113198 q = 1) (hb : d141767 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113198, d141767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113198, d141767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113199 q = 1) (hb : d141768 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113199, d141768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113199, d141768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113203 q = 1) (hb : d141772 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113203, d141772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113203, d141772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26083 q ha hb
  have h12 (q : Pattern) (ha : d113205 q = 1) (hb : d141774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113205, d141774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113205, d141774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26084 q ha hb
  have h13 (q : Pattern) (ha : d113206 q = 1) (hb : d141775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113206, d141775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113206, d141775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113207 q = 1) (hb : d141776 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113207, d141776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113207, d141776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113208 q = 1) (hb : d141777 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113208, d141777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113208, d141777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113209 q = 1) (hb : d141778 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113209, d141778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113209, d141778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113265 q = 1) (hb : d141816 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113265, d141816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113265, d141816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26091 q ha hb
  have h18 (q : Pattern) (ha : d113272 q = 1) (hb : d141827 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113272, d141827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113272, d141827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26093 q ha hb
  have h19 (q : Pattern) (ha : d113273 q = 1) (hb : d141828 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113273, d141828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113273, d141828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113274 q = 1) (hb : d141829 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113274, d141829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113274, d141829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113275 q = 1) (hb : d141830 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113275, d141830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113275, d141830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113276 q = 1) (hb : d141831 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113276, d141831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113276, d141831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113277 q = 1) (hb : d141832 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113277, d141832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113277, d141832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26095 (p : Pattern) (ha : d113283 p = 1) (hb : d141838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113278 q = 1) (hb : d141833 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113278, d141833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113278, d141833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26094 q ha hb
  have h2 (q : Pattern) (ha : d113279 q = 1) (hb : d141834 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113279, d141834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113279, d141834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113280 q = 1) (hb : d141835 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113280, d141835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113280, d141835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113281 q = 1) (hb : d141836 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113281, d141836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113281, d141836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113282 q = 1) (hb : d141837 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113282, d141837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113282, d141837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113283 q = 1) (hb : d141838 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113283, d141838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113283, d141838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26096 (p : Pattern) (ha : d113297 p = 1) (hb : d141843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113287 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113287, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18644 q hb ha
    | true =>
      simp only [d113287, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113288 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113288, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113288, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113289 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113289, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113289, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69113 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69114 q = 1) (hb : d88641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q hb ha
    | true =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69115 q = 1) (hb : d88642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69116 q = 1) (hb : d88643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113290 q = 1) (hb : d141841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113290, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113290, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113291 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d88641 q = 1) (hb : d113292 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88641, d113292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q ha hb
    | true =>
      simp only [d88641, d113292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d88642 q = 1) (hb : d113293 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88642, d113293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88642, d113293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d88643 q = 1) (hb : d113294 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88643, d113294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88643, d113294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88644 q = 1) (hb : d113295 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88644, d113295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88644, d113295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d113296 q = 1) (hb : d141842 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113296, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113296, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113297 q = 1) (hb : d141843 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113297, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113297, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro26097 (p : Pattern) (ha : d113301 p = 1) (hb : d141847 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113291 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d88641 q = 1) (hb : d113292 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88641, d113292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q ha hb
    | true =>
      simp only [d88641, d113292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88642 q = 1) (hb : d113293 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88642, d113293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88642, d113293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88643 q = 1) (hb : d113294 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88643, d113294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88643, d113294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88644 q = 1) (hb : d113295 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88644, d113295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88644, d113295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d113300 q = 1) (hb : d141846 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113300, d141846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d113300, d141846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113301 q = 1) (hb : d141847 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113301, d141847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113301, d141847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26098 (p : Pattern) (ha : d113307 p = 1) (hb : d141853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26096 q ha hb
    | true =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113306 q = 1) (hb : d141852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113306, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113306, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113307 q = 1) (hb : d141853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113307, d141853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113307, d141853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26099 (p : Pattern) (ha : d113311 p = 1) (hb : d141857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113309 q = 1) (hb : d141855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113309, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113309, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113310 q = 1) (hb : d141856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113310, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113310, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113311 q = 1) (hb : d141857 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113311, d141857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113311, d141857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26100 (p : Pattern) (ha : d113317 p = 1) (hb : d141863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113312 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26098 q ha hb
    | true =>
      simp only [d113312, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26099 q ha hb
  have h2 (q : Pattern) (ha : d113313 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113313, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113313, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113314 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113314, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113314, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113315 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113315, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113315, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113316 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113316, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113316, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113317 q = 1) (hb : d141863 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113317, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113317, d141863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26101 (p : Pattern) (ha : d113320 p = 1) (hb : d141866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26096 q ha hb
    | true =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113306 q = 1) (hb : d141852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113306, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113306, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113320 q = 1) (hb : d141866 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113320, d141866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113320, d141866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26102 (p : Pattern) (ha : d113321 p = 1) (hb : d141867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113309 q = 1) (hb : d141855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113309, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113309, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113310 q = 1) (hb : d141856 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113310, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113310, d141856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113321 q = 1) (hb : d141867 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113321, d141867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113321, d141867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26103 (p : Pattern) (ha : d113327 p = 1) (hb : d141873 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113312 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113312, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26098 q ha hb
    | true =>
      simp only [d113312, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26099 q ha hb
  have h2 (q : Pattern) (ha : d113313 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113313, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113313, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113314 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113314, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113314, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113315 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113315, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113315, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113316 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113316, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113316, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113322 q = 1) (hb : d141868 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113322, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26101 q ha hb
    | true =>
      simp only [d113322, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26102 q ha hb
  have h7 (q : Pattern) (ha : d113323 q = 1) (hb : d141869 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113323, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113323, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113324 q = 1) (hb : d141870 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113324, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113324, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113325 q = 1) (hb : d141871 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113325, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113325, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113326 q = 1) (hb : d141872 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113326, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113326, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113327 q = 1) (hb : d141873 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113327, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113327, d141873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26104 (p : Pattern) (ha : d113332 p = 1) (hb : d141878 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26096 q ha hb
    | true =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113331 q = 1) (hb : d141877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113331, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113331, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113332 q = 1) (hb : d141878 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113332, d141878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113332, d141878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26105 (p : Pattern) (ha : d113334 p = 1) (hb : d141880 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113309 q = 1) (hb : d141855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113309, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113309, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113333 q = 1) (hb : d141879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113333, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113333, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113334 q = 1) (hb : d141880 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113334, d141880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113334, d141880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26106 (p : Pattern) (ha : d113341 p = 1) (hb : d141887 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26096 q ha hb
    | true =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113339 q = 1) (hb : d141885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113339, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113339, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113340 q = 1) (hb : d141886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113340, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113340, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113341 q = 1) (hb : d141887 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113341, d141887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113341, d141887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26107 (p : Pattern) (ha : d113344 p = 1) (hb : d141890 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113342 q = 1) (hb : d141888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113342, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113342, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113343 q = 1) (hb : d141889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113343, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113343, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113344 q = 1) (hb : d141890 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113344, d141890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113344, d141890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26108 (p : Pattern) (ha : d113366 p = 1) (hb : d141899 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113286 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113349 q = 1) (hb : d141894 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113349, d141894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18654 q hb ha
    | true =>
      simp only [d113349, d141894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113350 q = 1) (hb : d141895 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113350, d141895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113350, d141895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113351 q = 1) (hb : d141896 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113351, d141896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113351, d141896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113360 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113361 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113361, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18644 q hb ha
    | true =>
      simp only [d113361, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113362 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113362, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113362, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113363 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113363, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113363, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113364 q = 1) (hb : d141897 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113364, d141897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113364, d141897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69099 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d113287 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113287, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18644 q hb ha
    | true =>
      simp only [d113287, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d113288 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113288, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113288, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113289 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113289, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113289, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69113 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69114 q = 1) (hb : d88641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q hb ha
    | true =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d69115 q = 1) (hb : d88642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69116 q = 1) (hb : d88643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113290 q = 1) (hb : d141841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113290, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113290, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113365 q = 1) (hb : d141898 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113365, d141898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113365, d141898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113366 q = 1) (hb : d141899 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113366, d141899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113366, d141899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26109 (p : Pattern) (ha : d113370 p = 1) (hb : d141843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69099 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113287 q = 1) (hb : d114586 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113287, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18644 q hb ha
    | true =>
      simp only [d113287, d114586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113288 q = 1) (hb : d114587 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113288, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113288, d114587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113289 q = 1) (hb : d114588 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113289, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113289, d114588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69113 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69114 q = 1) (hb : d88641 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7945 q hb ha
    | true =>
      simp only [d69114, d88641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69115 q = 1) (hb : d88642 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69115, d88642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69116 q = 1) (hb : d88643 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69116, d88643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113290 q = 1) (hb : d141841 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113290, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113290, d141841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69117 q = 1) (hb : d88644 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69117, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69117, d88644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113369 q = 1) (hb : d141842 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113369, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113369, d141842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113370 q = 1) (hb : d141843 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113370, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113370, d141843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26110 (p : Pattern) (ha : d113376 p = 1) (hb : d141905 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113367 q = 1) (hb : d141900 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113367, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26108 q ha hb
    | true =>
      simp only [d113367, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113368 q = 1) (hb : d141901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113368, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113368, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113371 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26109 q ha hb
    | true =>
      simp only [d113371, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113372 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113373 q = 1) (hb : d141902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113373, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113373, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113374 q = 1) (hb : d141903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113374, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113374, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113375 q = 1) (hb : d141904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113375, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113375, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113376 q = 1) (hb : d141905 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113376, d141905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113376, d141905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26111 (p : Pattern) (ha : d113380 p = 1) (hb : d141853 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113371 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26109 q ha hb
    | true =>
      simp only [d113371, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113372 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113377 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113377, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113377, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113378 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113378, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113378, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113379 q = 1) (hb : d141852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113379, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113379, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113380 q = 1) (hb : d141853 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113380, d141853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113380, d141853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26112 (p : Pattern) (ha : d113386 p = 1) (hb : d141911 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26096 q ha hb
    | true =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113383 q = 1) (hb : d141908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113383, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113383, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113384 q = 1) (hb : d141909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113384, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113384, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113385 q = 1) (hb : d141910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113385, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113385, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113386 q = 1) (hb : d141911 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113386, d141911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113386, d141911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26113 (p : Pattern) (ha : d113392 p = 1) (hb : d141917 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113335 q = 1) (hb : d141881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113335, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26104 q ha hb
    | true =>
      simp only [d113335, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26105 q ha hb
  have h2 (q : Pattern) (ha : d113336 q = 1) (hb : d141882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113336, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113336, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113337 q = 1) (hb : d141883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113337, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113337, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113338 q = 1) (hb : d141884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113338, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113338, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113345 q = 1) (hb : d141891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113345, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26106 q ha hb
    | true =>
      simp only [d113345, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26107 q ha hb
  have h6 (q : Pattern) (ha : d113346 q = 1) (hb : d141892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113346, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113346, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113347 q = 1) (hb : d141893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113347, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113347, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113381 q = 1) (hb : d141906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113381, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26110 q ha hb
    | true =>
      simp only [d113381, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26111 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113312 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113382 q = 1) (hb : d141907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113382, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113387 q = 1) (hb : d141912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113387, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26112 q ha hb
    | true =>
      simp only [d113387, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113388 q = 1) (hb : d141913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113388, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113388, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113389 q = 1) (hb : d141914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113389, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113390 q = 1) (hb : d141915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113390, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113391 q = 1) (hb : d141916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113391, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113392 q = 1) (hb : d141917 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113392, d141917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113392, d141917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26114 (p : Pattern) (ha : d113393 p = 1) (hb : d141918 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26096 q ha hb
    | true =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113305 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113305, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113305, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113331 q = 1) (hb : d141877 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113331, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113331, d141877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113393 q = 1) (hb : d141918 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113393, d141918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113393, d141918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26115 (p : Pattern) (ha : d113394 p = 1) (hb : d141919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113309 q = 1) (hb : d141855 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113309, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113309, d141855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113333 q = 1) (hb : d141879 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113333, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113333, d141879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113394 q = 1) (hb : d141919 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113394, d141919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113394, d141919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26116 (p : Pattern) (ha : d113399 p = 1) (hb : d141924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26096 q ha hb
    | true =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113304 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113304, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113339 q = 1) (hb : d141885 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113339, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113339, d141885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113340 q = 1) (hb : d141886 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113340, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113340, d141886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113399 q = 1) (hb : d141924 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113399, d141924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113399, d141924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26117 (p : Pattern) (ha : d113400 p = 1) (hb : d141925 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113308 q = 1) (hb : d141854 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113308, d141854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113342 q = 1) (hb : d141888 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113342, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113342, d141888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113343 q = 1) (hb : d141889 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113343, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113343, d141889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113400 q = 1) (hb : d141925 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113400, d141925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113400, d141925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26118 (p : Pattern) (ha : d113404 p = 1) (hb : d141929 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113367 q = 1) (hb : d141900 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113367, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26108 q ha hb
    | true =>
      simp only [d113367, d141900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113368 q = 1) (hb : d141901 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113368, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113368, d141901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113371 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26109 q ha hb
    | true =>
      simp only [d113371, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113372 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113373 q = 1) (hb : d141902 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113373, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113373, d141902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113374 q = 1) (hb : d141903 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113374, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113374, d141903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113375 q = 1) (hb : d141904 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113375, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113375, d141904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113404 q = 1) (hb : d141929 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113404, d141929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113404, d141929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26119 (p : Pattern) (ha : d113405 p = 1) (hb : d141866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113371 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113371, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26109 q ha hb
    | true =>
      simp only [d113371, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113372 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113372, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113372, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113302 q = 1) (hb : d141848 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26097 q ha hb
    | true =>
      simp only [d113302, d141848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113303 q = 1) (hb : d141849 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113303, d141849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113377 q = 1) (hb : d141850 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113377, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113377, d141850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113378 q = 1) (hb : d141851 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113378, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113378, d141851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113379 q = 1) (hb : d141852 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113379, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113379, d141852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113405 q = 1) (hb : d141866 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113405, d141866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113405, d141866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26120 (p : Pattern) (ha : d113408 p = 1) (hb : d141932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113298 q = 1) (hb : d141844 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26096 q ha hb
    | true =>
      simp only [d113298, d141844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113299 q = 1) (hb : d141845 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113299, d141845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113383 q = 1) (hb : d141908 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113383, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113383, d141908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113384 q = 1) (hb : d141909 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113384, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113384, d141909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113385 q = 1) (hb : d141910 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113385, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113385, d141910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113408 q = 1) (hb : d141932 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113408, d141932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113408, d141932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26121 (p : Pattern) (ha : d113414 p = 1) (hb : d141938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113335 q = 1) (hb : d141881 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113335, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26104 q ha hb
    | true =>
      simp only [d113335, d141881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26105 q ha hb
  have h2 (q : Pattern) (ha : d113336 q = 1) (hb : d141882 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113336, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113336, d141882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113337 q = 1) (hb : d141883 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113337, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113337, d141883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113338 q = 1) (hb : d141884 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113338, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113338, d141884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113345 q = 1) (hb : d141891 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113345, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26106 q ha hb
    | true =>
      simp only [d113345, d141891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26107 q ha hb
  have h6 (q : Pattern) (ha : d113346 q = 1) (hb : d141892 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113346, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113346, d141892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113347 q = 1) (hb : d141893 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113347, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113347, d141893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113381 q = 1) (hb : d141906 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113381, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26110 q ha hb
    | true =>
      simp only [d113381, d141906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26111 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113312 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113382 q = 1) (hb : d141907 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113382, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113382, d141907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113387 q = 1) (hb : d141912 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113387, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26112 q ha hb
    | true =>
      simp only [d113387, d141912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113388 q = 1) (hb : d141913 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113388, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113388, d141913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113389 q = 1) (hb : d141914 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113389, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113389, d141914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113390 q = 1) (hb : d141915 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113390, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113390, d141915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113391 q = 1) (hb : d141916 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113391, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113391, d141916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113395 q = 1) (hb : d141920 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113395, d141920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26114 q ha hb
    | true =>
      simp only [d113395, d141920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26115 q ha hb
  have h17 (q : Pattern) (ha : d113396 q = 1) (hb : d141921 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113396, d141921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113396, d141921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113397 q = 1) (hb : d141922 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113397, d141922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113397, d141922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113398 q = 1) (hb : d141923 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113398, d141923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113398, d141923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113401 q = 1) (hb : d141926 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113401, d141926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26116 q ha hb
    | true =>
      simp only [d113401, d141926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26117 q ha hb
  have h21 (q : Pattern) (ha : d113402 q = 1) (hb : d141927 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113402, d141927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113402, d141927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113403 q = 1) (hb : d141928 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113403, d141928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113403, d141928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113406 q = 1) (hb : d141930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113406, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26118 q ha hb
    | true =>
      simp only [d113406, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26119 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113322 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113407 q = 1) (hb : d141931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113407, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113409 q = 1) (hb : d141933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113409, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26120 q ha hb
    | true =>
      simp only [d113409, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113410 q = 1) (hb : d141934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113410, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113410, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113411 q = 1) (hb : d141935 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113411, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113412 q = 1) (hb : d141936 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113412, d141936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113412, d141936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113413 q = 1) (hb : d141937 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113413, d141937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113413, d141937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113414 q = 1) (hb : d141938 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113414, d141938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113414, d141938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26122 (p : Pattern) (ha : d113426 p = 1) (hb : d141945 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113416 q = 1) (hb : d141858 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113416, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26111 q ha hb
    | true =>
      simp only [d113416, d141858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26099 q ha hb
  have h2 (q : Pattern) (ha : d113417 q = 1) (hb : d141859 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113417, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113417, d141859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113418 q = 1) (hb : d141860 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113418, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113418, d141860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113419 q = 1) (hb : d141861 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113419, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113419, d141861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113420 q = 1) (hb : d141862 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113420, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113420, d141862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113421 q = 1) (hb : d141940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113421, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26099 q ha hb
    | true =>
      simp only [d113421, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113422 q = 1) (hb : d141941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113422, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113422, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113423 q = 1) (hb : d141942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113423, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113423, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113424 q = 1) (hb : d141943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113424, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113424, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113425 q = 1) (hb : d141944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113425, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113425, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113426 q = 1) (hb : d141945 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113426, d141945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113426, d141945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26123 (p : Pattern) (ha : d113432 p = 1) (hb : d141951 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113421 q = 1) (hb : d141940 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113421, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26099 q ha hb
    | true =>
      simp only [d113421, d141940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113422 q = 1) (hb : d141941 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113422, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113422, d141941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113423 q = 1) (hb : d141942 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113423, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113423, d141942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113424 q = 1) (hb : d141943 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113424, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113424, d141943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113425 q = 1) (hb : d141944 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113425, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113425, d141944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113427 q = 1) (hb : d141946 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113427, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26102 q ha hb
    | true =>
      simp only [d113427, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113428 q = 1) (hb : d141947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113428, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113428, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113429 q = 1) (hb : d141948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113429, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113429, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113430 q = 1) (hb : d141949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113430, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113430, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113431 q = 1) (hb : d141950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113431, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113431, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113432 q = 1) (hb : d141951 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113432, d141951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113432, d141951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26124 (p : Pattern) (ha : d113439 p = 1) (hb : d141958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113406 q = 1) (hb : d141930 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113406, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26118 q ha hb
    | true =>
      simp only [d113406, d141930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26119 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113322 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113407 q = 1) (hb : d141931 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113407, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113407, d141931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113409 q = 1) (hb : d141933 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113409, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26120 q ha hb
    | true =>
      simp only [d113409, d141933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113410 q = 1) (hb : d141934 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113410, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113410, d141934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113411 q = 1) (hb : d141935 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113411, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113411, d141935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113437 q = 1) (hb : d141956 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113437, d141956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113437, d141956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113438 q = 1) (hb : d141957 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113438, d141957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113438, d141957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113439 q = 1) (hb : d141958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113439, d141958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113439, d141958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26125 (p : Pattern) (ha : d113441 p = 1) (hb : d141960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113427 q = 1) (hb : d141946 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113427, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26102 q ha hb
    | true =>
      simp only [d113427, d141946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113428 q = 1) (hb : d141947 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113428, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113428, d141947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113429 q = 1) (hb : d141948 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113429, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113429, d141948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113430 q = 1) (hb : d141949 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113430, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113430, d141949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113431 q = 1) (hb : d141950 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113431, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113431, d141950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113441 q = 1) (hb : d141960 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113441, d141960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113441, d141960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26126 (p : Pattern) (ha : d113471 p = 1) (hb : d141972 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113448 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113449 q = 1) (hb : d141966 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113449, d141966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18671 q hb ha
    | true =>
      simp only [d113449, d141966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113450 q = 1) (hb : d141967 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113450, d141967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113450, d141967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113451 q = 1) (hb : d141968 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113451, d141968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113451, d141968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113461 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113462 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113462, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18672 q hb ha
    | true =>
      simp only [d113462, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113463 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113463, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113463, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113464 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113464, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113464, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113465 q = 1) (hb : d141969 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113465, d141969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113465, d141969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76089 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d113466 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113466, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18672 q hb ha
    | true =>
      simp only [d113466, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d113467 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113467, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113467, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113468 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113468, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113468, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76095 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76096 q = 1) (hb : d88705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q hb ha
    | true =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76097 q = 1) (hb : d88706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76098 q = 1) (hb : d88707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113469 q = 1) (hb : d141970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113469, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113469, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113470 q = 1) (hb : d141971 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113470, d141971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113470, d141971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113471 q = 1) (hb : d141972 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113471, d141972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113471, d141972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26127 (p : Pattern) (ha : d113475 p = 1) (hb : d141976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76089 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113466 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113466, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18672 q hb ha
    | true =>
      simp only [d113466, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113467 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113467, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113467, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113468 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113468, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113468, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76095 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76096 q = 1) (hb : d88705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q hb ha
    | true =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76097 q = 1) (hb : d88706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76098 q = 1) (hb : d88707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113469 q = 1) (hb : d141970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113469, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113469, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76099 q = 1) (hb : d88708 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76099, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76099, d88708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113474 q = 1) (hb : d141975 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113474, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113474, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113475 q = 1) (hb : d141976 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113475, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113475, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26128 (p : Pattern) (ha : d113481 p = 1) (hb : d141982 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113472 q = 1) (hb : d141973 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113472, d141973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26126 q ha hb
    | true =>
      simp only [d113472, d141973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113473 q = 1) (hb : d141974 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113473, d141974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113473, d141974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113476 q = 1) (hb : d141977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113476, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26127 q ha hb
    | true =>
      simp only [d113476, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113477 q = 1) (hb : d141978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113477, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113477, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113478 q = 1) (hb : d141979 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113478, d141979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113478, d141979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113479 q = 1) (hb : d141980 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113479, d141980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113479, d141980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113480 q = 1) (hb : d141981 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113480, d141981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113480, d141981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113481 q = 1) (hb : d141982 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113481, d141982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113481, d141982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26129 (p : Pattern) (ha : d113488 p = 1) (hb : d141984 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113482 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d88705 q = 1) (hb : d113483 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88705, d113483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q ha hb
    | true =>
      simp only [d88705, d113483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88706 q = 1) (hb : d113484 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88706, d113484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88706, d113484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88707 q = 1) (hb : d113485 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88707, d113485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88707, d113485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88708 q = 1) (hb : d113486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88708, d113486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88708, d113486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d113487 q = 1) (hb : d141983 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113487, d141983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d113487, d141983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113488 q = 1) (hb : d141984 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113488, d141984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113488, d141984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26130 (p : Pattern) (ha : d113494 p = 1) (hb : d141990 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113476 q = 1) (hb : d141977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113476, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26127 q ha hb
    | true =>
      simp only [d113476, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113477 q = 1) (hb : d141978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113477, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113477, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113489 q = 1) (hb : d141985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113489, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26129 q ha hb
    | true =>
      simp only [d113489, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113490 q = 1) (hb : d141986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113490, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113490, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113491 q = 1) (hb : d141987 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113491, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113491, d141987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113492 q = 1) (hb : d141988 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113492, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113492, d141988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113493 q = 1) (hb : d141989 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113493, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113493, d141989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113494 q = 1) (hb : d141990 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113494, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113494, d141990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26131 (p : Pattern) (ha : d113497 p = 1) (hb : d141976 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76089 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113466 q = 1) (hb : d114643 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113466, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18672 q hb ha
    | true =>
      simp only [d113466, d114643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113467 q = 1) (hb : d114644 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113467, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113467, d114644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113468 q = 1) (hb : d114645 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113468, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113468, d114645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76095 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76096 q = 1) (hb : d88705 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q hb ha
    | true =>
      simp only [d76096, d88705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76097 q = 1) (hb : d88706 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76097, d88706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76098 q = 1) (hb : d88707 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76098, d88707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113469 q = 1) (hb : d141970 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113469, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113469, d141970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113482 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d88705 q = 1) (hb : d113483 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88705, d113483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10886 q ha hb
    | true =>
      simp only [d88705, d113483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d88706 q = 1) (hb : d113484 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88706, d113484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88706, d113484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d88707 q = 1) (hb : d113485 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88707, d113485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88707, d113485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88708 q = 1) (hb : d113486 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88708, d113486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88708, d113486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d113496 q = 1) (hb : d141975 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113496, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113496, d141975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113497 q = 1) (hb : d141976 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113497, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113497, d141976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro26132 (p : Pattern) (ha : d113513 p = 1) (hb : d141996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113498 q = 1) (hb : d141977 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113498, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26131 q ha hb
    | true =>
      simp only [d113498, d141977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113499 q = 1) (hb : d141978 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113499, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113499, d141978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113510 q = 1) (hb : d141993 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113510, d141993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113510, d141993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113511 q = 1) (hb : d141994 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113511, d141994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113511, d141994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113512 q = 1) (hb : d141995 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113512, d141995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113512, d141995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113513 q = 1) (hb : d141996 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113513, d141996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113513, d141996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26133 (p : Pattern) (ha : d113519 p = 1) (hb : d142002 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113495 q = 1) (hb : d141991 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113495, d141991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26128 q ha hb
    | true =>
      simp only [d113495, d141991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26130 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113508 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113509 q = 1) (hb : d141992 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113509, d141992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113509, d141992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113514 q = 1) (hb : d141997 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113514, d141997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26132 q ha hb
    | true =>
      simp only [d113514, d141997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113515 q = 1) (hb : d141998 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113515, d141998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113515, d141998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113516 q = 1) (hb : d141999 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113516, d141999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113516, d141999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113517 q = 1) (hb : d142000 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113517, d142000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113517, d142000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113518 q = 1) (hb : d142001 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113518, d142001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113518, d142001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113519 q = 1) (hb : d142002 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113519, d142002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113519, d142002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26134 (p : Pattern) (ha : d113507 p = 1) (hb : d142007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113489 q = 1) (hb : d141985 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113489, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26129 q ha hb
    | true =>
      simp only [d113489, d141985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113490 q = 1) (hb : d141986 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113490, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113490, d141986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113504 q = 1) (hb : d142004 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113504, d142004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113504, d142004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113505 q = 1) (hb : d142005 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113505, d142005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113505, d142005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113506 q = 1) (hb : d142006 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113506, d142006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113506, d142006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113507 q = 1) (hb : d142007 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113507, d142007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113507, d142007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26135 (p : Pattern) (ha : d113526 p = 1) (hb : d142013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113521 q = 1) (hb : d142008 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113521, d142008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26134 q ha hb
    | true =>
      simp only [d113521, d142008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113522 q = 1) (hb : d142009 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113522, d142009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113522, d142009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113523 q = 1) (hb : d142010 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113523, d142010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113523, d142010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113524 q = 1) (hb : d142011 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113524, d142011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113524, d142011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113525 q = 1) (hb : d142012 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113525, d142012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113525, d142012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113526 q = 1) (hb : d142013 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113526, d142013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113526, d142013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26136 (p : Pattern) (ha : d113532 p = 1) (hb : d142019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113318 q = 1) (hb : d141864 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113318, d141864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113318, d141864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26100 q ha hb
  have h2 (q : Pattern) (ha : d113319 q = 1) (hb : d141865 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113319, d141865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113319, d141865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113328 q = 1) (hb : d141874 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113328, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26100 q ha hb
    | true =>
      simp only [d113328, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26103 q ha hb
  have h4 (q : Pattern) (ha : d113329 q = 1) (hb : d141875 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113329, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113329, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113330 q = 1) (hb : d141876 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113330, d141876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113330, d141876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113415 q = 1) (hb : d141939 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113415, d141939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26113 q ha hb
    | true =>
      simp only [d113415, d141939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26121 q ha hb
  have h7 (q : Pattern) (ha : d113433 q = 1) (hb : d141952 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113433, d141952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26122 q ha hb
    | true =>
      simp only [d113433, d141952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26123 q ha hb
  have h8 (q : Pattern) (ha : d113434 q = 1) (hb : d141953 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113434, d141953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113434, d141953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113435 q = 1) (hb : d141954 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113435, d141954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113435, d141954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113436 q = 1) (hb : d141955 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113436, d141955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113436, d141955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113440 q = 1) (hb : d141959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113440, d141959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113440, d141959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26124 q ha hb
  have h12 (q : Pattern) (ha : d113442 q = 1) (hb : d141961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113442, d141961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113442, d141961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26125 q ha hb
  have h13 (q : Pattern) (ha : d113443 q = 1) (hb : d141962 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113443, d141962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113443, d141962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113444 q = 1) (hb : d141963 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113444, d141963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113444, d141963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113445 q = 1) (hb : d141964 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113445, d141964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113445, d141964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113446 q = 1) (hb : d141965 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113446, d141965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113446, d141965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113520 q = 1) (hb : d142003 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113520, d142003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113520, d142003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26133 q ha hb
  have h18 (q : Pattern) (ha : d113527 q = 1) (hb : d142014 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113527, d142014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113527, d142014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26135 q ha hb
  have h19 (q : Pattern) (ha : d113528 q = 1) (hb : d142015 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113528, d142015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113528, d142015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113529 q = 1) (hb : d142016 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113529, d142016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113529, d142016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113530 q = 1) (hb : d142017 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113530, d142017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113530, d142017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113531 q = 1) (hb : d142018 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113531, d142018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113531, d142018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113532 q = 1) (hb : d142019 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113532, d142019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113532, d142019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26137 (p : Pattern) (ha : d113538 p = 1) (hb : d142025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113533 q = 1) (hb : d142020 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113533, d142020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113533, d142020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26136 q ha hb
  have h2 (q : Pattern) (ha : d113534 q = 1) (hb : d142021 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113534, d142021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113534, d142021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113535 q = 1) (hb : d142022 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113535, d142022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113535, d142022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113536 q = 1) (hb : d142023 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113536, d142023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113536, d142023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113537 q = 1) (hb : d142024 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113537, d142024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113537, d142024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113538 q = 1) (hb : d142025 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113538, d142025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113538, d142025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26138 (p : Pattern) (ha : d113553 p = 1) (hb : d142031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69207 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113543 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113543, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18692 q hb ha
    | true =>
      simp only [d113543, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113544 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113544, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113544, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113545 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113545, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113545, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69226 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69227 q = 1) (hb : d88794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q hb ha
    | true =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69228 q = 1) (hb : d88795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69229 q = 1) (hb : d88796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113546 q = 1) (hb : d142029 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113546, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113546, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113547 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d88794 q = 1) (hb : d113548 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88794, d113548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q ha hb
    | true =>
      simp only [d88794, d113548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d88795 q = 1) (hb : d113549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88795, d113549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88795, d113549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d88796 q = 1) (hb : d113550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88796, d113550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88796, d113550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88797 q = 1) (hb : d113551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88797, d113551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88797, d113551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d113552 q = 1) (hb : d142030 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113552, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113552, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113553 q = 1) (hb : d142031 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113553, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113553, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro26139 (p : Pattern) (ha : d113557 p = 1) (hb : d142035 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113547 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d88794 q = 1) (hb : d113548 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88794, d113548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q ha hb
    | true =>
      simp only [d88794, d113548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88795 q = 1) (hb : d113549 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88795, d113549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88795, d113549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88796 q = 1) (hb : d113550 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88796, d113550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88796, d113550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88797 q = 1) (hb : d113551 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88797, d113551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88797, d113551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d113556 q = 1) (hb : d142034 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113556, d142034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d113556, d142034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113557 q = 1) (hb : d142035 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113557, d142035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113557, d142035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26140 (p : Pattern) (ha : d113563 p = 1) (hb : d142041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26138 q ha hb
    | true =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113562 q = 1) (hb : d142040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113562, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113562, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113563 q = 1) (hb : d142041 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113563, d142041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113563, d142041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26141 (p : Pattern) (ha : d113567 p = 1) (hb : d142045 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113565 q = 1) (hb : d142043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113565, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113565, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113566 q = 1) (hb : d142044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113566, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113566, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113567 q = 1) (hb : d142045 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113567, d142045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113567, d142045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26142 (p : Pattern) (ha : d113573 p = 1) (hb : d142051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113568 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26140 q ha hb
    | true =>
      simp only [d113568, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26141 q ha hb
  have h2 (q : Pattern) (ha : d113569 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113569, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113569, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113570 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113570, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113570, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113571 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113571, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113571, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113572 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113572, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113572, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113573 q = 1) (hb : d142051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113573, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113573, d142051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26143 (p : Pattern) (ha : d113576 p = 1) (hb : d142054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26138 q ha hb
    | true =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113562 q = 1) (hb : d142040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113562, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113562, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113576 q = 1) (hb : d142054 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113576, d142054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113576, d142054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26144 (p : Pattern) (ha : d113577 p = 1) (hb : d142055 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113565 q = 1) (hb : d142043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113565, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113565, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113566 q = 1) (hb : d142044 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113566, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113566, d142044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113577 q = 1) (hb : d142055 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113577, d142055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113577, d142055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26145 (p : Pattern) (ha : d113583 p = 1) (hb : d142061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113568 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113568, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26140 q ha hb
    | true =>
      simp only [d113568, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26141 q ha hb
  have h2 (q : Pattern) (ha : d113569 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113569, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113569, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113570 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113570, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113570, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113571 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113571, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113571, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113572 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113572, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113572, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113578 q = 1) (hb : d142056 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113578, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26143 q ha hb
    | true =>
      simp only [d113578, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26144 q ha hb
  have h7 (q : Pattern) (ha : d113579 q = 1) (hb : d142057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113579, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113579, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113580 q = 1) (hb : d142058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113580, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113580, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113581 q = 1) (hb : d142059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113581, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113581, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113582 q = 1) (hb : d142060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113582, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113582, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113583 q = 1) (hb : d142061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113583, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113583, d142061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26146 (p : Pattern) (ha : d113588 p = 1) (hb : d142066 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26138 q ha hb
    | true =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113587 q = 1) (hb : d142065 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113587, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113587, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113588 q = 1) (hb : d142066 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113588, d142066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113588, d142066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26147 (p : Pattern) (ha : d113590 p = 1) (hb : d142068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113565 q = 1) (hb : d142043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113565, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113565, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113589 q = 1) (hb : d142067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113589, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113589, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113590 q = 1) (hb : d142068 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113590, d142068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113590, d142068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26148 (p : Pattern) (ha : d113597 p = 1) (hb : d142075 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26138 q ha hb
    | true =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113595 q = 1) (hb : d142073 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113595, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113595, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113596 q = 1) (hb : d142074 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113596, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113596, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113597 q = 1) (hb : d142075 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113597, d142075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113597, d142075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26149 (p : Pattern) (ha : d113600 p = 1) (hb : d142078 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113598 q = 1) (hb : d142076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113598, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113598, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113599 q = 1) (hb : d142077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113599, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113599, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113600 q = 1) (hb : d142078 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113600, d142078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113600, d142078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26150 (p : Pattern) (ha : d113622 p = 1) (hb : d142087 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113542 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113605 q = 1) (hb : d142082 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113605, d142082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18702 q hb ha
    | true =>
      simp only [d113605, d142082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113606 q = 1) (hb : d142083 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113606, d142083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113606, d142083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113607 q = 1) (hb : d142084 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113607, d142084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113607, d142084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113616 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113617 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113617, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18692 q hb ha
    | true =>
      simp only [d113617, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113618 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113618, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113618, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113619 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113619, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113619, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113620 q = 1) (hb : d142085 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113620, d142085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113620, d142085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69207 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d113543 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113543, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18692 q hb ha
    | true =>
      simp only [d113543, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d113544 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113544, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113544, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113545 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113545, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113545, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69226 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69227 q = 1) (hb : d88794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q hb ha
    | true =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d69228 q = 1) (hb : d88795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69229 q = 1) (hb : d88796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113546 q = 1) (hb : d142029 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113546, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113546, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113621 q = 1) (hb : d142086 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113621, d142086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113621, d142086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113622 q = 1) (hb : d142087 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113622, d142087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113622, d142087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26151 (p : Pattern) (ha : d113626 p = 1) (hb : d142031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69207 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113543 q = 1) (hb : d114730 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113543, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18692 q hb ha
    | true =>
      simp only [d113543, d114730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113544 q = 1) (hb : d114731 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113544, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113544, d114731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113545 q = 1) (hb : d114732 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113545, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113545, d114732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69226 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69227 q = 1) (hb : d88794 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7962 q hb ha
    | true =>
      simp only [d69227, d88794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69228 q = 1) (hb : d88795 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69228, d88795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69229 q = 1) (hb : d88796 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69229, d88796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113546 q = 1) (hb : d142029 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113546, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113546, d142029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69230 q = 1) (hb : d88797 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69230, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69230, d88797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113625 q = 1) (hb : d142030 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113625, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113625, d142030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113626 q = 1) (hb : d142031 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113626, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113626, d142031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26152 (p : Pattern) (ha : d113632 p = 1) (hb : d142093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113623 q = 1) (hb : d142088 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113623, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26150 q ha hb
    | true =>
      simp only [d113623, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113624 q = 1) (hb : d142089 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113624, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113624, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113627 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26151 q ha hb
    | true =>
      simp only [d113627, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113628 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113629 q = 1) (hb : d142090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113629, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113629, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113630 q = 1) (hb : d142091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113630, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113630, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113631 q = 1) (hb : d142092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113631, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113631, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113632 q = 1) (hb : d142093 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113632, d142093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113632, d142093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26153 (p : Pattern) (ha : d113636 p = 1) (hb : d142041 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113627 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26151 q ha hb
    | true =>
      simp only [d113627, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113628 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113633 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113633, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113633, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113634 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113634, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113634, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113635 q = 1) (hb : d142040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113635, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113635, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113636 q = 1) (hb : d142041 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113636, d142041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113636, d142041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26154 (p : Pattern) (ha : d113642 p = 1) (hb : d142099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26138 q ha hb
    | true =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113639 q = 1) (hb : d142096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113639, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113639, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113640 q = 1) (hb : d142097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113640, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113640, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113641 q = 1) (hb : d142098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113641, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113641, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113642 q = 1) (hb : d142099 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113642, d142099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113642, d142099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26155 (p : Pattern) (ha : d113648 p = 1) (hb : d142105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113591 q = 1) (hb : d142069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113591, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26146 q ha hb
    | true =>
      simp only [d113591, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26147 q ha hb
  have h2 (q : Pattern) (ha : d113592 q = 1) (hb : d142070 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113592, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113592, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113593 q = 1) (hb : d142071 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113593, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113593, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113594 q = 1) (hb : d142072 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113594, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113594, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113601 q = 1) (hb : d142079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113601, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26148 q ha hb
    | true =>
      simp only [d113601, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26149 q ha hb
  have h6 (q : Pattern) (ha : d113602 q = 1) (hb : d142080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113602, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113602, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113603 q = 1) (hb : d142081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113603, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113603, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113637 q = 1) (hb : d142094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113637, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26152 q ha hb
    | true =>
      simp only [d113637, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26153 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113568 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113638 q = 1) (hb : d142095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113638, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113643 q = 1) (hb : d142100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113643, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26154 q ha hb
    | true =>
      simp only [d113643, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113644 q = 1) (hb : d142101 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113644, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113644, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113645 q = 1) (hb : d142102 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113645, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113646 q = 1) (hb : d142103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113646, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113647 q = 1) (hb : d142104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113647, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113648 q = 1) (hb : d142105 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113648, d142105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113648, d142105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26156 (p : Pattern) (ha : d113649 p = 1) (hb : d142106 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26138 q ha hb
    | true =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113561 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113561, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113561, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113587 q = 1) (hb : d142065 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113587, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113587, d142065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113649 q = 1) (hb : d142106 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113649, d142106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113649, d142106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26157 (p : Pattern) (ha : d113650 p = 1) (hb : d142107 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113565 q = 1) (hb : d142043 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113565, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113565, d142043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113589 q = 1) (hb : d142067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113589, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113589, d142067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113650 q = 1) (hb : d142107 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113650, d142107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113650, d142107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26158 (p : Pattern) (ha : d113655 p = 1) (hb : d142112 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26138 q ha hb
    | true =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113560 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113560, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113595 q = 1) (hb : d142073 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113595, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113595, d142073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113596 q = 1) (hb : d142074 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113596, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113596, d142074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113655 q = 1) (hb : d142112 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113655, d142112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113655, d142112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26159 (p : Pattern) (ha : d113656 p = 1) (hb : d142113 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113564 q = 1) (hb : d142042 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113564, d142042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113598 q = 1) (hb : d142076 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113598, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113598, d142076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113599 q = 1) (hb : d142077 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113599, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113599, d142077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113656 q = 1) (hb : d142113 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113656, d142113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113656, d142113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26160 (p : Pattern) (ha : d113660 p = 1) (hb : d142117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113623 q = 1) (hb : d142088 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113623, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26150 q ha hb
    | true =>
      simp only [d113623, d142088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113624 q = 1) (hb : d142089 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113624, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113624, d142089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113627 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26151 q ha hb
    | true =>
      simp only [d113627, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113628 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113629 q = 1) (hb : d142090 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113629, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113629, d142090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113630 q = 1) (hb : d142091 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113630, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113630, d142091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113631 q = 1) (hb : d142092 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113631, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113631, d142092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113660 q = 1) (hb : d142117 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113660, d142117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113660, d142117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26161 (p : Pattern) (ha : d113661 p = 1) (hb : d142054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113627 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113627, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26151 q ha hb
    | true =>
      simp only [d113627, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113628 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113628, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113628, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113558 q = 1) (hb : d142036 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26139 q ha hb
    | true =>
      simp only [d113558, d142036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113559 q = 1) (hb : d142037 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113559, d142037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113633 q = 1) (hb : d142038 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113633, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113633, d142038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113634 q = 1) (hb : d142039 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113634, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113634, d142039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113635 q = 1) (hb : d142040 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113635, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113635, d142040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113661 q = 1) (hb : d142054 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113661, d142054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113661, d142054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26162 (p : Pattern) (ha : d113664 p = 1) (hb : d142120 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113554 q = 1) (hb : d142032 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26138 q ha hb
    | true =>
      simp only [d113554, d142032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113555 q = 1) (hb : d142033 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113555, d142033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113639 q = 1) (hb : d142096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113639, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113639, d142096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113640 q = 1) (hb : d142097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113640, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113640, d142097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113641 q = 1) (hb : d142098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113641, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113641, d142098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113664 q = 1) (hb : d142120 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113664, d142120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113664, d142120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26163 (p : Pattern) (ha : d113670 p = 1) (hb : d142126 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113591 q = 1) (hb : d142069 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113591, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26146 q ha hb
    | true =>
      simp only [d113591, d142069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26147 q ha hb
  have h2 (q : Pattern) (ha : d113592 q = 1) (hb : d142070 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113592, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113592, d142070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113593 q = 1) (hb : d142071 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113593, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113593, d142071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113594 q = 1) (hb : d142072 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113594, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113594, d142072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113601 q = 1) (hb : d142079 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113601, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26148 q ha hb
    | true =>
      simp only [d113601, d142079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26149 q ha hb
  have h6 (q : Pattern) (ha : d113602 q = 1) (hb : d142080 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113602, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113602, d142080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113603 q = 1) (hb : d142081 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113603, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113603, d142081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113637 q = 1) (hb : d142094 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113637, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26152 q ha hb
    | true =>
      simp only [d113637, d142094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26153 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113568 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113638 q = 1) (hb : d142095 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113638, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113638, d142095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113643 q = 1) (hb : d142100 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113643, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26154 q ha hb
    | true =>
      simp only [d113643, d142100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113644 q = 1) (hb : d142101 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113644, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113644, d142101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113645 q = 1) (hb : d142102 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113645, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113645, d142102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113646 q = 1) (hb : d142103 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113646, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113646, d142103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113647 q = 1) (hb : d142104 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113647, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113647, d142104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113651 q = 1) (hb : d142108 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113651, d142108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26156 q ha hb
    | true =>
      simp only [d113651, d142108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26157 q ha hb
  have h17 (q : Pattern) (ha : d113652 q = 1) (hb : d142109 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113652, d142109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113652, d142109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113653 q = 1) (hb : d142110 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113653, d142110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113653, d142110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113654 q = 1) (hb : d142111 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113654, d142111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113654, d142111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113657 q = 1) (hb : d142114 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113657, d142114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26158 q ha hb
    | true =>
      simp only [d113657, d142114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26159 q ha hb
  have h21 (q : Pattern) (ha : d113658 q = 1) (hb : d142115 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113658, d142115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113658, d142115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113659 q = 1) (hb : d142116 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113659, d142116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113659, d142116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113662 q = 1) (hb : d142118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113662, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26160 q ha hb
    | true =>
      simp only [d113662, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26161 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113578 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113663 q = 1) (hb : d142119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113663, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113665 q = 1) (hb : d142121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113665, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26162 q ha hb
    | true =>
      simp only [d113665, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113666 q = 1) (hb : d142122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113666, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113666, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113667 q = 1) (hb : d142123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113667, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113668 q = 1) (hb : d142124 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113668, d142124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113668, d142124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113669 q = 1) (hb : d142125 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113669, d142125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113669, d142125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113670 q = 1) (hb : d142126 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113670, d142126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113670, d142126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26164 (p : Pattern) (ha : d113682 p = 1) (hb : d142133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113672 q = 1) (hb : d142046 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113672, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26153 q ha hb
    | true =>
      simp only [d113672, d142046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26141 q ha hb
  have h2 (q : Pattern) (ha : d113673 q = 1) (hb : d142047 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113673, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113673, d142047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113674 q = 1) (hb : d142048 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113674, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113674, d142048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113675 q = 1) (hb : d142049 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113675, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113675, d142049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113676 q = 1) (hb : d142050 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113676, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113676, d142050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113677 q = 1) (hb : d142128 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113677, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26141 q ha hb
    | true =>
      simp only [d113677, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113678 q = 1) (hb : d142129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113678, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113678, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113679 q = 1) (hb : d142130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113679, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113679, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113680 q = 1) (hb : d142131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113680, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113680, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113681 q = 1) (hb : d142132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113681, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113681, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113682 q = 1) (hb : d142133 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113682, d142133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113682, d142133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26165 (p : Pattern) (ha : d113688 p = 1) (hb : d142139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113677 q = 1) (hb : d142128 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113677, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26141 q ha hb
    | true =>
      simp only [d113677, d142128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113678 q = 1) (hb : d142129 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113678, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113678, d142129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113679 q = 1) (hb : d142130 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113679, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113679, d142130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113680 q = 1) (hb : d142131 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113680, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113680, d142131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113681 q = 1) (hb : d142132 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113681, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113681, d142132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113683 q = 1) (hb : d142134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113683, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26144 q ha hb
    | true =>
      simp only [d113683, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113684 q = 1) (hb : d142135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113684, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113684, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113685 q = 1) (hb : d142136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113685, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113685, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113686 q = 1) (hb : d142137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113686, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113686, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113687 q = 1) (hb : d142138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113687, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113687, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113688 q = 1) (hb : d142139 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113688, d142139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113688, d142139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26166 (p : Pattern) (ha : d113695 p = 1) (hb : d142146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113662 q = 1) (hb : d142118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113662, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26160 q ha hb
    | true =>
      simp only [d113662, d142118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26161 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113578 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113663 q = 1) (hb : d142119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113663, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113663, d142119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113665 q = 1) (hb : d142121 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113665, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26162 q ha hb
    | true =>
      simp only [d113665, d142121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113666 q = 1) (hb : d142122 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113666, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113666, d142122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113667 q = 1) (hb : d142123 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113667, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113667, d142123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113693 q = 1) (hb : d142144 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113693, d142144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113693, d142144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113694 q = 1) (hb : d142145 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113694, d142145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113694, d142145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113695 q = 1) (hb : d142146 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113695, d142146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113695, d142146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26167 (p : Pattern) (ha : d113697 p = 1) (hb : d142148 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113683 q = 1) (hb : d142134 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113683, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26144 q ha hb
    | true =>
      simp only [d113683, d142134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113684 q = 1) (hb : d142135 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113684, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113684, d142135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113685 q = 1) (hb : d142136 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113685, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113685, d142136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113686 q = 1) (hb : d142137 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113686, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113686, d142137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113687 q = 1) (hb : d142138 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113687, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113687, d142138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113697 q = 1) (hb : d142148 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113697, d142148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113697, d142148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26168 (p : Pattern) (ha : d113727 p = 1) (hb : d142160 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113704 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113705 q = 1) (hb : d142154 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113705, d142154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18719 q hb ha
    | true =>
      simp only [d113705, d142154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113706 q = 1) (hb : d142155 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113706, d142155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113706, d142155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113707 q = 1) (hb : d142156 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113707, d142156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113707, d142156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113717 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113718 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113718, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18720 q hb ha
    | true =>
      simp only [d113718, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113719 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113719, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113719, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113720 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113720, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113720, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113721 q = 1) (hb : d142157 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113721, d142157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113721, d142157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76224 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d113722 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18720 q hb ha
    | true =>
      simp only [d113722, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d113723 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113724 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76230 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76231 q = 1) (hb : d88858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q hb ha
    | true =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76232 q = 1) (hb : d88859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76233 q = 1) (hb : d88860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113725 q = 1) (hb : d142158 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113725, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113726 q = 1) (hb : d142159 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113726, d142159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113726, d142159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113727 q = 1) (hb : d142160 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113727, d142160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113727, d142160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26169 (p : Pattern) (ha : d113731 p = 1) (hb : d142164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76224 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113722 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18720 q hb ha
    | true =>
      simp only [d113722, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113723 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113724 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76230 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76231 q = 1) (hb : d88858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q hb ha
    | true =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76232 q = 1) (hb : d88859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76233 q = 1) (hb : d88860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113725 q = 1) (hb : d142158 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113725, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76234 q = 1) (hb : d88861 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76234, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76234, d88861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113730 q = 1) (hb : d142163 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113730, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113730, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113731 q = 1) (hb : d142164 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113731, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113731, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26170 (p : Pattern) (ha : d113737 p = 1) (hb : d142170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113728 q = 1) (hb : d142161 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113728, d142161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26168 q ha hb
    | true =>
      simp only [d113728, d142161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113729 q = 1) (hb : d142162 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113729, d142162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113729, d142162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113732 q = 1) (hb : d142165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113732, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26169 q ha hb
    | true =>
      simp only [d113732, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113733 q = 1) (hb : d142166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113733, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113733, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113734 q = 1) (hb : d142167 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113734, d142167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113734, d142167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113735 q = 1) (hb : d142168 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113735, d142168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113735, d142168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113736 q = 1) (hb : d142169 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113736, d142169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113736, d142169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113737 q = 1) (hb : d142170 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113737, d142170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113737, d142170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26171 (p : Pattern) (ha : d113744 p = 1) (hb : d142172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113738 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d88858 q = 1) (hb : d113739 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88858, d113739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q ha hb
    | true =>
      simp only [d88858, d113739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88859 q = 1) (hb : d113740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88859, d113740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88859, d113740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88860 q = 1) (hb : d113741 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88860, d113741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88860, d113741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88861 q = 1) (hb : d113742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88861, d113742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88861, d113742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d113743 q = 1) (hb : d142171 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113743, d142171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d113743, d142171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113744 q = 1) (hb : d142172 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113744, d142172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113744, d142172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26172 (p : Pattern) (ha : d113750 p = 1) (hb : d142178 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113732 q = 1) (hb : d142165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113732, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26169 q ha hb
    | true =>
      simp only [d113732, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113733 q = 1) (hb : d142166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113733, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113733, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113745 q = 1) (hb : d142173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26171 q ha hb
    | true =>
      simp only [d113745, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113746 q = 1) (hb : d142174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113747 q = 1) (hb : d142175 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113747, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113747, d142175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113748 q = 1) (hb : d142176 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113748, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113748, d142176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113749 q = 1) (hb : d142177 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113749, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113749, d142177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113750 q = 1) (hb : d142178 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113750, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113750, d142178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26173 (p : Pattern) (ha : d113753 p = 1) (hb : d142164 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76224 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113722 q = 1) (hb : d114787 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113722, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18720 q hb ha
    | true =>
      simp only [d113722, d114787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113723 q = 1) (hb : d114788 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113723, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113723, d114788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113724 q = 1) (hb : d114789 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113724, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113724, d114789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76230 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76231 q = 1) (hb : d88858 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q hb ha
    | true =>
      simp only [d76231, d88858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76232 q = 1) (hb : d88859 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76232, d88859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76233 q = 1) (hb : d88860 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76233, d88860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113725 q = 1) (hb : d142158 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113725, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113725, d142158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113738 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d88858 q = 1) (hb : d113739 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88858, d113739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10900 q ha hb
    | true =>
      simp only [d88858, d113739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d88859 q = 1) (hb : d113740 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88859, d113740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88859, d113740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d88860 q = 1) (hb : d113741 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88860, d113741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88860, d113741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88861 q = 1) (hb : d113742 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88861, d113742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88861, d113742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d113752 q = 1) (hb : d142163 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113752, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113752, d142163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113753 q = 1) (hb : d142164 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113753, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113753, d142164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro26174 (p : Pattern) (ha : d113769 p = 1) (hb : d142184 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113754 q = 1) (hb : d142165 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113754, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26173 q ha hb
    | true =>
      simp only [d113754, d142165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113755 q = 1) (hb : d142166 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113755, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113755, d142166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113766 q = 1) (hb : d142181 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113766, d142181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113766, d142181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113767 q = 1) (hb : d142182 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113767, d142182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113767, d142182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113768 q = 1) (hb : d142183 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113768, d142183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113768, d142183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113769 q = 1) (hb : d142184 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113769, d142184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113769, d142184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26175 (p : Pattern) (ha : d113775 p = 1) (hb : d142190 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113751 q = 1) (hb : d142179 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113751, d142179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26170 q ha hb
    | true =>
      simp only [d113751, d142179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26172 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113764 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113765 q = 1) (hb : d142180 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113765, d142180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113765, d142180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113770 q = 1) (hb : d142185 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113770, d142185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26174 q ha hb
    | true =>
      simp only [d113770, d142185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113771 q = 1) (hb : d142186 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113771, d142186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113771, d142186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113772 q = 1) (hb : d142187 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113772, d142187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113772, d142187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113773 q = 1) (hb : d142188 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113773, d142188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113773, d142188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113774 q = 1) (hb : d142189 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113774, d142189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113774, d142189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113775 q = 1) (hb : d142190 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113775, d142190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113775, d142190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26176 (p : Pattern) (ha : d113763 p = 1) (hb : d142195 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113745 q = 1) (hb : d142173 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113745, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26171 q ha hb
    | true =>
      simp only [d113745, d142173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113746 q = 1) (hb : d142174 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113746, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113746, d142174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113760 q = 1) (hb : d142192 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113760, d142192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113760, d142192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113761 q = 1) (hb : d142193 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113761, d142193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113761, d142193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113762 q = 1) (hb : d142194 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113762, d142194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113762, d142194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113763 q = 1) (hb : d142195 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113763, d142195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113763, d142195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26177 (p : Pattern) (ha : d113782 p = 1) (hb : d142201 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113777 q = 1) (hb : d142196 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113777, d142196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26176 q ha hb
    | true =>
      simp only [d113777, d142196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113778 q = 1) (hb : d142197 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113778, d142197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113778, d142197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113779 q = 1) (hb : d142198 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113779, d142198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113779, d142198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113780 q = 1) (hb : d142199 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113780, d142199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113780, d142199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113781 q = 1) (hb : d142200 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113781, d142200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113781, d142200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113782 q = 1) (hb : d142201 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113782, d142201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113782, d142201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26178 (p : Pattern) (ha : d113788 p = 1) (hb : d142207 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113574 q = 1) (hb : d142052 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113574, d142052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113574, d142052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26142 q ha hb
  have h2 (q : Pattern) (ha : d113575 q = 1) (hb : d142053 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113575, d142053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113575, d142053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113584 q = 1) (hb : d142062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113584, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26142 q ha hb
    | true =>
      simp only [d113584, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26145 q ha hb
  have h4 (q : Pattern) (ha : d113585 q = 1) (hb : d142063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113585, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113585, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113586 q = 1) (hb : d142064 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113586, d142064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113586, d142064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113671 q = 1) (hb : d142127 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113671, d142127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26155 q ha hb
    | true =>
      simp only [d113671, d142127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26163 q ha hb
  have h7 (q : Pattern) (ha : d113689 q = 1) (hb : d142140 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113689, d142140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26164 q ha hb
    | true =>
      simp only [d113689, d142140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26165 q ha hb
  have h8 (q : Pattern) (ha : d113690 q = 1) (hb : d142141 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113690, d142141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113690, d142141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113691 q = 1) (hb : d142142 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113691, d142142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113691, d142142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113692 q = 1) (hb : d142143 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113692, d142143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113692, d142143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113696 q = 1) (hb : d142147 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113696, d142147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113696, d142147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26166 q ha hb
  have h12 (q : Pattern) (ha : d113698 q = 1) (hb : d142149 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113698, d142149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113698, d142149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26167 q ha hb
  have h13 (q : Pattern) (ha : d113699 q = 1) (hb : d142150 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113699, d142150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113699, d142150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113700 q = 1) (hb : d142151 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113700, d142151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113700, d142151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113701 q = 1) (hb : d142152 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113701, d142152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113701, d142152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113702 q = 1) (hb : d142153 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113702, d142153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113702, d142153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d113776 q = 1) (hb : d142191 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113776, d142191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113776, d142191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26175 q ha hb
  have h18 (q : Pattern) (ha : d113783 q = 1) (hb : d142202 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113783, d142202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113783, d142202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26177 q ha hb
  have h19 (q : Pattern) (ha : d113784 q = 1) (hb : d142203 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113784, d142203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113784, d142203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113785 q = 1) (hb : d142204 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113785, d142204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113785, d142204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d113786 q = 1) (hb : d142205 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113786, d142205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d113786, d142205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d113787 q = 1) (hb : d142206 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113787, d142206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113787, d142206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113788 q = 1) (hb : d142207 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d113788, d142207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d113788, d142207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26179 (p : Pattern) (ha : d113794 p = 1) (hb : d142213 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113789 q = 1) (hb : d142208 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d113789, d142208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113789, d142208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26178 q ha hb
  have h2 (q : Pattern) (ha : d113790 q = 1) (hb : d142209 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d113790, d142209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113790, d142209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113791 q = 1) (hb : d142210 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d113791, d142210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113791, d142210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113792 q = 1) (hb : d142211 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d113792, d142211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113792, d142211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113793 q = 1) (hb : d142212 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d113793, d142212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113793, d142212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113794 q = 1) (hb : d142213 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d113794, d142213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113794, d142213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26180 (p : Pattern) (ha : d113810 p = 1) (hb : d142220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113800 q = 1) (hb : d114875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18740 q hb ha
    | true =>
      simp only [d113800, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113801 q = 1) (hb : d114876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113802 q = 1) (hb : d114877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69336 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69337 q = 1) (hb : d88948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q hb ha
    | true =>
      simp only [d69337, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69338 q = 1) (hb : d88949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69339 q = 1) (hb : d88950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113803 q = 1) (hb : d142218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113803, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113804 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d88948 q = 1) (hb : d113805 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88948, d113805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q ha hb
    | true =>
      simp only [d88948, d113805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d88949 q = 1) (hb : d113806 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88949, d113806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88949, d113806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d88950 q = 1) (hb : d113807 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88950, d113807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88950, d113807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d88951 q = 1) (hb : d113808 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88951, d113808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d88951, d113808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d113809 q = 1) (hb : d142219 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113809, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113809, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d113810 q = 1) (hb : d142220 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113810, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113810, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro26181 (p : Pattern) (ha : d113814 p = 1) (hb : d142224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113804 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d88948 q = 1) (hb : d113805 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d88948, d113805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q ha hb
    | true =>
      simp only [d88948, d113805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d88949 q = 1) (hb : d113806 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d88949, d113806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88949, d113806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d88950 q = 1) (hb : d113807 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d88950, d113807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d88950, d113807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d88951 q = 1) (hb : d113808 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d88951, d113808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d88951, d113808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d113813 q = 1) (hb : d142223 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113813, d142223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d113813, d142223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113814 q = 1) (hb : d142224 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113814, d142224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113814, d142224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26182 (p : Pattern) (ha : d113820 p = 1) (hb : d142230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26180 q ha hb
    | true =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113819 q = 1) (hb : d142229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113819, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113819, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113820 q = 1) (hb : d142230 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113820, d142230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113820, d142230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26183 (p : Pattern) (ha : d113824 p = 1) (hb : d142234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d142232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113823 q = 1) (hb : d142233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113823, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113823, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113824 q = 1) (hb : d142234 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113824, d142234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113824, d142234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26184 (p : Pattern) (ha : d113830 p = 1) (hb : d142240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113825 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26182 q ha hb
    | true =>
      simp only [d113825, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26183 q ha hb
  have h2 (q : Pattern) (ha : d113826 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113826, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113826, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113827 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113827, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113827, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113828 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113828, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113828, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113829 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113829, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113829, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113830 q = 1) (hb : d142240 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113830, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113830, d142240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26185 (p : Pattern) (ha : d113833 p = 1) (hb : d142243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26180 q ha hb
    | true =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113819 q = 1) (hb : d142229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113819, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113819, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113833 q = 1) (hb : d142243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113833, d142243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113833, d142243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26186 (p : Pattern) (ha : d113834 p = 1) (hb : d142244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d142232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113823 q = 1) (hb : d142233 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113823, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113823, d142233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113834 q = 1) (hb : d142244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113834, d142244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113834, d142244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26187 (p : Pattern) (ha : d113840 p = 1) (hb : d142250 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113825 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113825, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26182 q ha hb
    | true =>
      simp only [d113825, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26183 q ha hb
  have h2 (q : Pattern) (ha : d113826 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113826, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113826, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113827 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113827, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113827, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113828 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113828, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113828, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113829 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113829, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113829, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113835 q = 1) (hb : d142245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113835, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26185 q ha hb
    | true =>
      simp only [d113835, d142245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26186 q ha hb
  have h7 (q : Pattern) (ha : d113836 q = 1) (hb : d142246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113836, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113836, d142246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113837 q = 1) (hb : d142247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113837, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113837, d142247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113838 q = 1) (hb : d142248 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113838, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113838, d142248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113839 q = 1) (hb : d142249 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113839, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113839, d142249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113840 q = 1) (hb : d142250 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113840, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113840, d142250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26188 (p : Pattern) (ha : d113845 p = 1) (hb : d142255 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26180 q ha hb
    | true =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113844 q = 1) (hb : d142254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113844, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113844, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113845 q = 1) (hb : d142255 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113845, d142255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113845, d142255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26189 (p : Pattern) (ha : d113847 p = 1) (hb : d142257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d142232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113846 q = 1) (hb : d142256 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113846, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113846, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113847 q = 1) (hb : d142257 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113847, d142257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113847, d142257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26190 (p : Pattern) (ha : d113854 p = 1) (hb : d142264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26180 q ha hb
    | true =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113852 q = 1) (hb : d142262 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113852, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113852, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113853 q = 1) (hb : d142263 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113853, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113853, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113854 q = 1) (hb : d142264 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113854, d142264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113854, d142264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26191 (p : Pattern) (ha : d113857 p = 1) (hb : d142267 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113855 q = 1) (hb : d142265 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113855, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113855, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113856 q = 1) (hb : d142266 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113856, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113856, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113857 q = 1) (hb : d142267 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113857, d142267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113857, d142267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26192 (p : Pattern) (ha : d113879 p = 1) (hb : d142276 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113799 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113862 q = 1) (hb : d142271 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113862, d142271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18750 q hb ha
    | true =>
      simp only [d113862, d142271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113863 q = 1) (hb : d142272 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113863, d142272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113863, d142272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113864 q = 1) (hb : d142273 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113864, d142273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113864, d142273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113873 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113874 q = 1) (hb : d114875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113874, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18740 q hb ha
    | true =>
      simp only [d113874, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113875 q = 1) (hb : d114876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113875, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113875, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113876 q = 1) (hb : d114877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113876, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113876, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113877 q = 1) (hb : d142274 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113877, d142274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113877, d142274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d69321 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d113800 q = 1) (hb : d114875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18740 q hb ha
    | true =>
      simp only [d113800, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d113801 q = 1) (hb : d114876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113802 q = 1) (hb : d114877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d69336 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d69337 q = 1) (hb : d88948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q hb ha
    | true =>
      simp only [d69337, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d69338 q = 1) (hb : d88949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d69339 q = 1) (hb : d88950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113803 q = 1) (hb : d142218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113803, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113878 q = 1) (hb : d142275 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113878, d142275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113878, d142275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113879 q = 1) (hb : d142276 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113879, d142276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113879, d142276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26193 (p : Pattern) (ha : d113883 p = 1) (hb : d142220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69321 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113800 q = 1) (hb : d114875 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113800, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18740 q hb ha
    | true =>
      simp only [d113800, d114875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113801 q = 1) (hb : d114876 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113801, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113801, d114876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113802 q = 1) (hb : d114877 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113802, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113802, d114877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69336 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d69337 q = 1) (hb : d88948 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d69337, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7979 q hb ha
    | true =>
      simp only [d69337, d88948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d69338 q = 1) (hb : d88949 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d69338, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69338, d88949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d69339 q = 1) (hb : d88950 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d69339, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d69339, d88950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113803 q = 1) (hb : d142218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113803, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113803, d142218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d69340 q = 1) (hb : d88951 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d69340, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d69340, d88951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113882 q = 1) (hb : d142219 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113882, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113882, d142219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113883 q = 1) (hb : d142220 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113883, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113883, d142220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26194 (p : Pattern) (ha : d113889 p = 1) (hb : d142282 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113880 q = 1) (hb : d142277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113880, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26192 q ha hb
    | true =>
      simp only [d113880, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113881 q = 1) (hb : d142278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113881, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113881, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113884 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26193 q ha hb
    | true =>
      simp only [d113884, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113885 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113886 q = 1) (hb : d142279 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113886, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113886, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113887 q = 1) (hb : d142280 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113887, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113887, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113888 q = 1) (hb : d142281 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113888, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113888, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113889 q = 1) (hb : d142282 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113889, d142282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113889, d142282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26195 (p : Pattern) (ha : d113893 p = 1) (hb : d142230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113884 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26193 q ha hb
    | true =>
      simp only [d113884, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113885 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113890 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113890, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113890, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113891 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113891, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113891, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113892 q = 1) (hb : d142229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113892, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113892, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113893 q = 1) (hb : d142230 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113893, d142230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113893, d142230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro26196 (p : Pattern) (ha : d113899 p = 1) (hb : d142288 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26180 q ha hb
    | true =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113896 q = 1) (hb : d142285 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113896, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113896, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113897 q = 1) (hb : d142286 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113897, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113897, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113898 q = 1) (hb : d142287 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113898, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113898, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113899 q = 1) (hb : d142288 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113899, d142288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113899, d142288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26197 (p : Pattern) (ha : d113905 p = 1) (hb : d142294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113848 q = 1) (hb : d142258 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113848, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26188 q ha hb
    | true =>
      simp only [d113848, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26189 q ha hb
  have h2 (q : Pattern) (ha : d113849 q = 1) (hb : d142259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113849, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113849, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113850 q = 1) (hb : d142260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113850, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113850, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113851 q = 1) (hb : d142261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113851, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113851, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113858 q = 1) (hb : d142268 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113858, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26190 q ha hb
    | true =>
      simp only [d113858, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26191 q ha hb
  have h6 (q : Pattern) (ha : d113859 q = 1) (hb : d142269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113859, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113859, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113860 q = 1) (hb : d142270 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113860, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113860, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113894 q = 1) (hb : d142283 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113894, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26194 q ha hb
    | true =>
      simp only [d113894, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26195 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113825 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113895 q = 1) (hb : d142284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113895, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113900 q = 1) (hb : d142289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113900, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26196 q ha hb
    | true =>
      simp only [d113900, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113901 q = 1) (hb : d142290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113901, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113901, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113902 q = 1) (hb : d142291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113902, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113903 q = 1) (hb : d142292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113903, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113904 q = 1) (hb : d142293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113904, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113905 q = 1) (hb : d142294 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113905, d142294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113905, d142294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro26198 (p : Pattern) (ha : d113906 p = 1) (hb : d142295 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26180 q ha hb
    | true =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113818 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113818, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113818, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113844 q = 1) (hb : d142254 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113844, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113844, d142254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113906 q = 1) (hb : d142295 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113906, d142295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113906, d142295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26199 (p : Pattern) (ha : d113907 p = 1) (hb : d142296 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113822 q = 1) (hb : d142232 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113822, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113822, d142232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113846 q = 1) (hb : d142256 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113846, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113846, d142256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113907 q = 1) (hb : d142296 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113907, d142296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113907, d142296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26200 (p : Pattern) (ha : d113912 p = 1) (hb : d142301 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26180 q ha hb
    | true =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113817 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113817, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113852 q = 1) (hb : d142262 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113852, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113852, d142262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113853 q = 1) (hb : d142263 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113853, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113853, d142263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113912 q = 1) (hb : d142301 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113912, d142301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113912, d142301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26201 (p : Pattern) (ha : d113913 p = 1) (hb : d142302 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113821 q = 1) (hb : d142231 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113821, d142231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113855 q = 1) (hb : d142265 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113855, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113855, d142265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113856 q = 1) (hb : d142266 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113856, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113856, d142266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113913 q = 1) (hb : d142302 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113913, d142302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113913, d142302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26202 (p : Pattern) (ha : d113917 p = 1) (hb : d142306 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113880 q = 1) (hb : d142277 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113880, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26192 q ha hb
    | true =>
      simp only [d113880, d142277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113881 q = 1) (hb : d142278 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113881, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113881, d142278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113884 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26193 q ha hb
    | true =>
      simp only [d113884, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113885 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113886 q = 1) (hb : d142279 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113886, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113886, d142279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113887 q = 1) (hb : d142280 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113887, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113887, d142280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113888 q = 1) (hb : d142281 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113888, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113888, d142281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113917 q = 1) (hb : d142306 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113917, d142306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113917, d142306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26203 (p : Pattern) (ha : d113918 p = 1) (hb : d142243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113884 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113884, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26193 q ha hb
    | true =>
      simp only [d113884, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113885 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113885, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113885, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113815 q = 1) (hb : d142225 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26181 q ha hb
    | true =>
      simp only [d113815, d142225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113816 q = 1) (hb : d142226 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113816, d142226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113890 q = 1) (hb : d142227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113890, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113890, d142227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113891 q = 1) (hb : d142228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113891, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113891, d142228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113892 q = 1) (hb : d142229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113892, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113892, d142229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113918 q = 1) (hb : d142243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113918, d142243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113918, d142243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26204 (p : Pattern) (ha : d113921 p = 1) (hb : d142309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113811 q = 1) (hb : d142221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26180 q ha hb
    | true =>
      simp only [d113811, d142221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113812 q = 1) (hb : d142222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113812, d142222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113896 q = 1) (hb : d142285 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113896, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113896, d142285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113897 q = 1) (hb : d142286 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113897, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113897, d142286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113898 q = 1) (hb : d142287 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113898, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113898, d142287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113921 q = 1) (hb : d142309 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113921, d142309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113921, d142309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26205 (p : Pattern) (ha : d113927 p = 1) (hb : d142315 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113848 q = 1) (hb : d142258 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113848, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26188 q ha hb
    | true =>
      simp only [d113848, d142258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26189 q ha hb
  have h2 (q : Pattern) (ha : d113849 q = 1) (hb : d142259 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113849, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113849, d142259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113850 q = 1) (hb : d142260 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113850, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113850, d142260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113851 q = 1) (hb : d142261 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113851, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113851, d142261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113858 q = 1) (hb : d142268 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113858, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26190 q ha hb
    | true =>
      simp only [d113858, d142268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26191 q ha hb
  have h6 (q : Pattern) (ha : d113859 q = 1) (hb : d142269 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113859, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113859, d142269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113860 q = 1) (hb : d142270 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113860, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113860, d142270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113894 q = 1) (hb : d142283 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113894, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26194 q ha hb
    | true =>
      simp only [d113894, d142283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26195 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d113825 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d113895 q = 1) (hb : d142284 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113895, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113895, d142284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d113900 q = 1) (hb : d142289 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113900, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26196 q ha hb
    | true =>
      simp only [d113900, d142289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d113901 q = 1) (hb : d142290 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113901, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113901, d142290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d113902 q = 1) (hb : d142291 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113902, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113902, d142291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113903 q = 1) (hb : d142292 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113903, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113903, d142292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d113904 q = 1) (hb : d142293 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113904, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113904, d142293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d113908 q = 1) (hb : d142297 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113908, d142297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26198 q ha hb
    | true =>
      simp only [d113908, d142297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26199 q ha hb
  have h17 (q : Pattern) (ha : d113909 q = 1) (hb : d142298 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113909, d142298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113909, d142298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113910 q = 1) (hb : d142299 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113910, d142299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d113910, d142299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d113911 q = 1) (hb : d142300 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113911, d142300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113911, d142300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113914 q = 1) (hb : d142303 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113914, d142303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26200 q ha hb
    | true =>
      simp only [d113914, d142303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26201 q ha hb
  have h21 (q : Pattern) (ha : d113915 q = 1) (hb : d142304 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113915, d142304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113915, d142304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d113916 q = 1) (hb : d142305 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113916, d142305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d113916, d142305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d113919 q = 1) (hb : d142307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113919, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26202 q ha hb
    | true =>
      simp only [d113919, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26203 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d113835 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d113920 q = 1) (hb : d142308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d113920, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d113922 q = 1) (hb : d142310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113922, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26204 q ha hb
    | true =>
      simp only [d113922, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d113923 q = 1) (hb : d142311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113923, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d113923, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d113924 q = 1) (hb : d142312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d113924, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d113925 q = 1) (hb : d142313 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113925, d142313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d113925, d142313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d113926 q = 1) (hb : d142314 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113926, d142314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113926, d142314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d113927 q = 1) (hb : d142315 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113927, d142315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d113927, d142315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro26206 (p : Pattern) (ha : d113939 p = 1) (hb : d142322 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113929 q = 1) (hb : d142235 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113929, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26195 q ha hb
    | true =>
      simp only [d113929, d142235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26183 q ha hb
  have h2 (q : Pattern) (ha : d113930 q = 1) (hb : d142236 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113930, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113930, d142236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113931 q = 1) (hb : d142237 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113931, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113931, d142237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113932 q = 1) (hb : d142238 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113932, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113932, d142238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113933 q = 1) (hb : d142239 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113933, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113933, d142239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113934 q = 1) (hb : d142317 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113934, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26183 q ha hb
    | true =>
      simp only [d113934, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113935 q = 1) (hb : d142318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113935, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113935, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113936 q = 1) (hb : d142319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113936, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113936, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113937 q = 1) (hb : d142320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113937, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113937, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113938 q = 1) (hb : d142321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113938, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113938, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113939 q = 1) (hb : d142322 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113939, d142322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113939, d142322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26207 (p : Pattern) (ha : d113945 p = 1) (hb : d142328 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113934 q = 1) (hb : d142317 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113934, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26183 q ha hb
    | true =>
      simp only [d113934, d142317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113935 q = 1) (hb : d142318 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113935, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113935, d142318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113936 q = 1) (hb : d142319 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113936, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113936, d142319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113937 q = 1) (hb : d142320 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113937, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113937, d142320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113938 q = 1) (hb : d142321 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113938, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113938, d142321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113940 q = 1) (hb : d142323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113940, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26186 q ha hb
    | true =>
      simp only [d113940, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113941 q = 1) (hb : d142324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113941, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113941, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113942 q = 1) (hb : d142325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113942, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113942, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d113943 q = 1) (hb : d142326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113943, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113943, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113944 q = 1) (hb : d142327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113944, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113944, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113945 q = 1) (hb : d142328 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113945, d142328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113945, d142328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro26208 (p : Pattern) (ha : d113952 p = 1) (hb : d142335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113919 q = 1) (hb : d142307 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113919, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26202 q ha hb
    | true =>
      simp only [d113919, d142307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26203 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d113835 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d113920 q = 1) (hb : d142308 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113920, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113920, d142308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d113922 q = 1) (hb : d142310 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113922, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26204 q ha hb
    | true =>
      simp only [d113922, d142310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113923 q = 1) (hb : d142311 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113923, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113923, d142311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d113924 q = 1) (hb : d142312 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113924, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113924, d142312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113950 q = 1) (hb : d142333 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113950, d142333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113950, d142333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113951 q = 1) (hb : d142334 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113951, d142334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113951, d142334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113952 q = 1) (hb : d142335 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113952, d142335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113952, d142335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26209 (p : Pattern) (ha : d113954 p = 1) (hb : d142337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113940 q = 1) (hb : d142323 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d113940, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26186 q ha hb
    | true =>
      simp only [d113940, d142323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113941 q = 1) (hb : d142324 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d113941, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113941, d142324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113942 q = 1) (hb : d142325 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d113942, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113942, d142325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113943 q = 1) (hb : d142326 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d113943, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113943, d142326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113944 q = 1) (hb : d142327 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d113944, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113944, d142327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113954 q = 1) (hb : d142337 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d113954, d142337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113954, d142337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26210 (p : Pattern) (ha : d113984 p = 1) (hb : d142349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113961 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113962 q = 1) (hb : d142343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113962, d142343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18767 q hb ha
    | true =>
      simp only [d113962, d142343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113963 q = 1) (hb : d142344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113963, d142344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113963, d142344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113964 q = 1) (hb : d142345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113964, d142345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113964, d142345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113974 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d113975 q = 1) (hb : d114932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113975, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18768 q hb ha
    | true =>
      simp only [d113975, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d113976 q = 1) (hb : d114933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113976, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113976, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d113977 q = 1) (hb : d114934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113977, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113977, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113978 q = 1) (hb : d142346 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113978, d142346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113978, d142346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d76360 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d113979 q = 1) (hb : d114932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18768 q hb ha
    | true =>
      simp only [d113979, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  have h12 (q : Pattern) (ha : d113980 q = 1) (hb : d114933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d113981 q = 1) (hb : d114934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d76366 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d76367 q = 1) (hb : d89012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q hb ha
    | true =>
      simp only [d76367, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d76368 q = 1) (hb : d89013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d76369 q = 1) (hb : d89014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d113982 q = 1) (hb : d142347 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113982, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d113983 q = 1) (hb : d142348 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113983, d142348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113983, d142348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d113984 q = 1) (hb : d142349 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113984, d142349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d113984, d142349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h20 p ha hb
theorem andIntro26211 (p : Pattern) (ha : d113988 p = 1) (hb : d142353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113979 q = 1) (hb : d114932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18768 q hb ha
    | true =>
      simp only [d113979, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113980 q = 1) (hb : d114933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113981 q = 1) (hb : d114934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76366 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76367 q = 1) (hb : d89012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q hb ha
    | true =>
      simp only [d76367, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76368 q = 1) (hb : d89013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76369 q = 1) (hb : d89014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113982 q = 1) (hb : d142347 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113982, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d76370 q = 1) (hb : d89015 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d76370, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d76370, d89015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d113987 q = 1) (hb : d142352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d113987, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d113987, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d113988 q = 1) (hb : d142353 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d113988, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113988, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h12 p ha hb
theorem andIntro26212 (p : Pattern) (ha : d113994 p = 1) (hb : d142359 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113985 q = 1) (hb : d142350 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113985, d142350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26210 q ha hb
    | true =>
      simp only [d113985, d142350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113986 q = 1) (hb : d142351 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113986, d142351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113986, d142351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d113989 q = 1) (hb : d142354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113989, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26211 q ha hb
    | true =>
      simp only [d113989, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d113990 q = 1) (hb : d142355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113990, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113990, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d113991 q = 1) (hb : d142356 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d113991, d142356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113991, d142356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113992 q = 1) (hb : d142357 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d113992, d142357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113992, d142357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d113993 q = 1) (hb : d142358 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d113993, d142358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113993, d142358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d113994 q = 1) (hb : d142359 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d113994, d142359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d113994, d142359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26213 (p : Pattern) (ha : d114001 p = 1) (hb : d142361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d113995 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d89012 q = 1) (hb : d113996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d89012, d113996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q ha hb
    | true =>
      simp only [d89012, d113996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d89013 q = 1) (hb : d113997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d89013, d113997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89013, d113997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d89014 q = 1) (hb : d113998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d89014, d113998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89014, d113998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d89015 q = 1) (hb : d113999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d89015, d113999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d89015, d113999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d114000 q = 1) (hb : d142360 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d114000, d142360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d114000, d142360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d114001 q = 1) (hb : d142361 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d114001, d142361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d114001, d142361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h7 p ha hb
theorem andIntro26214 (p : Pattern) (ha : d114007 p = 1) (hb : d142367 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113989 q = 1) (hb : d142354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d113989, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26211 q ha hb
    | true =>
      simp only [d113989, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d113990 q = 1) (hb : d142355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d113990, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113990, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114002 q = 1) (hb : d142362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26213 q ha hb
    | true =>
      simp only [d114002, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114003 q = 1) (hb : d142363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114004 q = 1) (hb : d142364 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114004, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114004, d142364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114005 q = 1) (hb : d142365 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114005, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114005, d142365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d114006 q = 1) (hb : d142366 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114006, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d114006, d142366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d114007 q = 1) (hb : d142367 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114007, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d114007, d142367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro26215 (p : Pattern) (ha : d114010 p = 1) (hb : d142353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d76360 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113979 q = 1) (hb : d114932 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d113979, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro18768 q hb ha
    | true =>
      simp only [d113979, d114932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h3 (q : Pattern) (ha : d113980 q = 1) (hb : d114933 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d113980, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113980, d114933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113981 q = 1) (hb : d114934 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d113981, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113981, d114934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d76366 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d76367 q = 1) (hb : d89012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d76367, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q hb ha
    | true =>
      simp only [d76367, d89012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d76368 q = 1) (hb : d89013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d76368, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76368, d89013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d76369 q = 1) (hb : d89014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d76369, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d76369, d89014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113982 q = 1) (hb : d142347 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d113982, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d113982, d142347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d113995 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d89012 q = 1) (hb : d113996 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d89012, d113996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro10914 q ha hb
    | true =>
      simp only [d89012, d113996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d89013 q = 1) (hb : d113997 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d89013, d113997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89013, d113997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d89014 q = 1) (hb : d113998 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d89014, d113998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d89014, d113998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d89015 q = 1) (hb : d113999 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d89015, d113999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d89015, d113999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d114009 q = 1) (hb : d142352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d114009, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d114009, d142352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d114010 q = 1) (hb : d142353 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d114010, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114010, d142353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro26216 (p : Pattern) (ha : d114026 p = 1) (hb : d142373 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114011 q = 1) (hb : d142354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114011, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26215 q ha hb
    | true =>
      simp only [d114011, d142354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114012 q = 1) (hb : d142355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114012, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114012, d142355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114023 q = 1) (hb : d142370 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114023, d142370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114023, d142370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114024 q = 1) (hb : d142371 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114024, d142371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114024, d142371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114025 q = 1) (hb : d142372 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114025, d142372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114025, d142372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114026 q = 1) (hb : d142373 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114026, d142373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114026, d142373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26217 (p : Pattern) (ha : d114032 p = 1) (hb : d142379 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114008 q = 1) (hb : d142368 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114008, d142368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26212 q ha hb
    | true =>
      simp only [d114008, d142368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26214 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d114021 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d114022 q = 1) (hb : d142369 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114022, d142369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114022, d142369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d114027 q = 1) (hb : d142374 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114027, d142374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26216 q ha hb
    | true =>
      simp only [d114027, d142374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114028 q = 1) (hb : d142375 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114028, d142375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114028, d142375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114029 q = 1) (hb : d142376 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114029, d142376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114029, d142376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d114030 q = 1) (hb : d142377 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114030, d142377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114030, d142377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d114031 q = 1) (hb : d142378 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114031, d142378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114031, d142378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d114032 q = 1) (hb : d142379 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114032, d142379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114032, d142379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro26218 (p : Pattern) (ha : d114020 p = 1) (hb : d142384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114002 q = 1) (hb : d142362 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d114002, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26213 q ha hb
    | true =>
      simp only [d114002, d142362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114003 q = 1) (hb : d142363 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d114003, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114003, d142363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114017 q = 1) (hb : d142381 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d114017, d142381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114017, d142381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114018 q = 1) (hb : d142382 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d114018, d142382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114018, d142382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114019 q = 1) (hb : d142383 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d114019, d142383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114019, d142383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114020 q = 1) (hb : d142384 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d114020, d142384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114020, d142384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26219 (p : Pattern) (ha : d114039 p = 1) (hb : d142390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114034 q = 1) (hb : d142385 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d114034, d142385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26218 q ha hb
    | true =>
      simp only [d114034, d142385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114035 q = 1) (hb : d142386 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d114035, d142386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114035, d142386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114036 q = 1) (hb : d142387 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d114036, d142387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114036, d142387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114037 q = 1) (hb : d142388 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d114037, d142388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114037, d142388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114038 q = 1) (hb : d142389 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d114038, d142389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114038, d142389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114039 q = 1) (hb : d142390 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d114039, d142390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114039, d142390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26220 (p : Pattern) (ha : d114045 p = 1) (hb : d142396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d113831 q = 1) (hb : d142241 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113831, d142241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113831, d142241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26184 q ha hb
  have h2 (q : Pattern) (ha : d113832 q = 1) (hb : d142242 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113832, d142242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113832, d142242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d113841 q = 1) (hb : d142251 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113841, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26184 q ha hb
    | true =>
      simp only [d113841, d142251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26187 q ha hb
  have h4 (q : Pattern) (ha : d113842 q = 1) (hb : d142252 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113842, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113842, d142252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d113843 q = 1) (hb : d142253 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113843, d142253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d113843, d142253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113928 q = 1) (hb : d142316 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113928, d142316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26197 q ha hb
    | true =>
      simp only [d113928, d142316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26205 q ha hb
  have h7 (q : Pattern) (ha : d113946 q = 1) (hb : d142329 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113946, d142329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26206 q ha hb
    | true =>
      simp only [d113946, d142329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26207 q ha hb
  have h8 (q : Pattern) (ha : d113947 q = 1) (hb : d142330 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113947, d142330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113947, d142330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113948 q = 1) (hb : d142331 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113948, d142331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d113948, d142331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d113949 q = 1) (hb : d142332 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113949, d142332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d113949, d142332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d113953 q = 1) (hb : d142336 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113953, d142336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113953, d142336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26208 q ha hb
  have h12 (q : Pattern) (ha : d113955 q = 1) (hb : d142338 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d113955, d142338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d113955, d142338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26209 q ha hb
  have h13 (q : Pattern) (ha : d113956 q = 1) (hb : d142339 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113956, d142339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d113956, d142339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d113957 q = 1) (hb : d142340 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d113957, d142340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d113957, d142340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d113958 q = 1) (hb : d142341 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d113958, d142341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d113958, d142341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d113959 q = 1) (hb : d142342 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d113959, d142342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d113959, d142342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d114033 q = 1) (hb : d142380 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114033, d142380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114033, d142380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26217 q ha hb
  have h18 (q : Pattern) (ha : d114040 q = 1) (hb : d142391 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d114040, d142391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114040, d142391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26219 q ha hb
  have h19 (q : Pattern) (ha : d114041 q = 1) (hb : d142392 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d114041, d142392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d114041, d142392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d114042 q = 1) (hb : d142393 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d114042, d142393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d114042, d142393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d114043 q = 1) (hb : d142394 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d114043, d142394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d114043, d142394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d114044 q = 1) (hb : d142395 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d114044, d142395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d114044, d142395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d114045 q = 1) (hb : d142396 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d114045, d142396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d114045, d142396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro26221 (p : Pattern) (ha : d114051 p = 1) (hb : d142402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114046 q = 1) (hb : d142397 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d114046, d142397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114046, d142397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26220 q ha hb
  have h2 (q : Pattern) (ha : d114047 q = 1) (hb : d142398 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d114047, d142398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114047, d142398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d114048 q = 1) (hb : d142399 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d114048, d142399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114048, d142399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d114049 q = 1) (hb : d142400 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d114049, d142400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114049, d142400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d114050 q = 1) (hb : d142401 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d114050, d142401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114050, d142401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d114051 q = 1) (hb : d142402 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d114051, d142402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d114051, d142402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26222 (p : Pattern) (ha : d114057 p = 1) (hb : d142408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d113073 q = 1) (hb : d141653 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113073, d141653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26019 q ha hb
    | true =>
      simp only [d113073, d141653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26057 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d113284 q = 1) (hb : d141839 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113284, d141839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113284, d141839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26095 q ha hb
  have h3 (q : Pattern) (ha : d113285 q = 1) (hb : d141840 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113285, d141840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d113285, d141840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d113539 q = 1) (hb : d142026 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113539, d142026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113539, d142026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26137 q ha hb
  have h5 (q : Pattern) (ha : d113540 q = 1) (hb : d142027 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113540, d142027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113540, d142027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d113541 q = 1) (hb : d142028 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113541, d142028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d113541, d142028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d113795 q = 1) (hb : d142214 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d113795, d142214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113795, d142214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26179 q ha hb
  have h8 (q : Pattern) (ha : d113796 q = 1) (hb : d142215 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d113796, d142215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113796, d142215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d113797 q = 1) (hb : d142216 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d113797, d142216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d113797, d142216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d113798 q = 1) (hb : d142217 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d113798, d142217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d113798, d142217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d114052 q = 1) (hb : d142403 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d114052, d142403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114052, d142403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26221 q ha hb
  have h12 (q : Pattern) (ha : d114053 q = 1) (hb : d142404 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d114053, d142404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114053, d142404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d114054 q = 1) (hb : d142405 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d114054, d142405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114054, d142405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d114055 q = 1) (hb : d142406 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d114055, d142406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d114055, d142406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d114056 q = 1) (hb : d142407 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d114056, d142407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d114056, d142407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d114057 q = 1) (hb : d142408 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d114057, d142408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d114057, d142408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro26223 (p : Pattern) (ha : d114063 p = 1) (hb : d142414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114058 q = 1) (hb : d142409 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d114058, d142409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26222 q ha hb
    | true =>
      simp only [d114058, d142409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114059 q = 1) (hb : d142410 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d114059, d142410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114059, d142410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114060 q = 1) (hb : d142411 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d114060, d142411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114060, d142411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114061 q = 1) (hb : d142412 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d114061, d142412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114061, d142412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114062 q = 1) (hb : d142413 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d114062, d142413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114062, d142413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114063 q = 1) (hb : d142414 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d114063, d142414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114063, d142414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26224 (p : Pattern) (ha : d114069 p = 1) (hb : d142420 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114064 q = 1) (hb : d142415 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d114064, d142415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26223 q ha hb
    | true =>
      simp only [d114064, d142415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114065 q = 1) (hb : d142416 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d114065, d142416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114065, d142416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114066 q = 1) (hb : d142417 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d114066, d142417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114066, d142417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114067 q = 1) (hb : d142418 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d114067, d142418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114067, d142418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114068 q = 1) (hb : d142419 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d114068, d142419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114068, d142419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114069 q = 1) (hb : d142420 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d114069, d142420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114069, d142420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26225 (p : Pattern) (ha : d114075 p = 1) (hb : d142426 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114070 q = 1) (hb : d142421 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d114070, d142421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26224 q ha hb
    | true =>
      simp only [d114070, d142421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114071 q = 1) (hb : d142422 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d114071, d142422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114071, d142422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114072 q = 1) (hb : d142423 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d114072, d142423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114072, d142423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114073 q = 1) (hb : d142424 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d114073, d142424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114073, d142424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114074 q = 1) (hb : d142425 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d114074, d142425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114074, d142425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114075 q = 1) (hb : d142426 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d114075, d142426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114075, d142426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26226 (p : Pattern) (ha : d114081 p = 1) (hb : d142432 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114076 q = 1) (hb : d142427 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d114076, d142427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26225 q ha hb
    | true =>
      simp only [d114076, d142427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114077 q = 1) (hb : d142428 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d114077, d142428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114077, d142428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114078 q = 1) (hb : d142429 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d114078, d142429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114078, d142429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114079 q = 1) (hb : d142430 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d114079, d142430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114079, d142430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114080 q = 1) (hb : d142431 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d114080, d142431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114080, d142431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114081 q = 1) (hb : d142432 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d114081, d142432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114081, d142432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26227 (p : Pattern) (ha : d114087 p = 1) (hb : d142438 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114082 q = 1) (hb : d142433 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d114082, d142433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26226 q ha hb
    | true =>
      simp only [d114082, d142433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114083 q = 1) (hb : d142434 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d114083, d142434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114083, d142434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114084 q = 1) (hb : d142435 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d114084, d142435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114084, d142435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114085 q = 1) (hb : d142436 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d114085, d142436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114085, d142436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114086 q = 1) (hb : d142437 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d114086, d142437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114086, d142437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114087 q = 1) (hb : d142438 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d114087, d142438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114087, d142438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26228 (p : Pattern) (ha : d114093 p = 1) (hb : d142444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114088 q = 1) (hb : d142439 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d114088, d142439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26227 q ha hb
    | true =>
      simp only [d114088, d142439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114089 q = 1) (hb : d142440 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d114089, d142440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114089, d142440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114090 q = 1) (hb : d142441 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d114090, d142441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114090, d142441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114091 q = 1) (hb : d142442 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d114091, d142442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114091, d142442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114092 q = 1) (hb : d142443 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d114092, d142443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114092, d142443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114093 q = 1) (hb : d142444 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d114093, d142444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114093, d142444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26229 (p : Pattern) (ha : d114099 p = 1) (hb : d142450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d114094 q = 1) (hb : d142445 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d114094, d142445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26228 q ha hb
    | true =>
      simp only [d114094, d142445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d114095 q = 1) (hb : d142446 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d114095, d142446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d114095, d142446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d114096 q = 1) (hb : d142447 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d114096, d142447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d114096, d142447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d114097 q = 1) (hb : d142448 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d114097, d142448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d114097, d142448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d114098 q = 1) (hb : d142449 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d114098, d142449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d114098, d142449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d114099 q = 1) (hb : d142450 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d114099, d142450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d114099, d142450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro26230 (p : Pattern) (ha : d109112 p = 1) (hb : d112686 p = 1) : d142453 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d112686 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10668 q = 1) (hb : d112686 q = 1) : d141318 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10668, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25747 q ha hb
    | true =>
      simp only [d10668, d141318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10722 q = 1) (hb : d112686 q = 1) : d141369 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10722, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10722, d141369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10723 q = 1) (hb : d112686 q = 1) : d141370 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10723, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10723, d141370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d10724 q = 1) (hb : d112686 q = 1) : d141371 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10724, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10724, d141371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d10725 q = 1) (hb : d112686 q = 1) : d141372 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10725, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10725, d141372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109112 q = 1) (hb : d112686 q = 1) : d142453 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109112, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109112, d142453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro26231 (p : Pattern) (ha : d109122 p = 1) (hb : d112686 p = 1) : d142463 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d112686 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10698 q = 1) (hb : d112686 q = 1) : d141345 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10698, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25751 q ha hb
    | true =>
      simp only [d10698, d141345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109118 q = 1) (hb : d112686 q = 1) : d142459 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109118, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109118, d142459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109119 q = 1) (hb : d112686 q = 1) : d142460 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109119, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d109119, d142460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d109120 q = 1) (hb : d112686 q = 1) : d142461 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109120, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109120, d142461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109121 q = 1) (hb : d112686 q = 1) : d142462 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109121, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109121, d142462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109122 q = 1) (hb : d112686 q = 1) : d142463 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109122, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109122, d142463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro26232 (p : Pattern) (ha : d109128 p = 1) (hb : d112686 p = 1) : d142469 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10727 q = 1) (hb : d112686 q = 1) : d141374 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10727, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25754 q ha hb
    | true =>
      simp only [d10727, d141374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25755 q ha hb
  have h2 (q : Pattern) (ha : d10728 q = 1) (hb : d112686 q = 1) : d141375 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10728, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10728, d141375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109110 q = 1) (hb : d112686 q = 1) : d142451 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109110, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109110, d142451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109111 q = 1) (hb : d112686 q = 1) : d142452 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109111, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109111, d142452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109113 q = 1) (hb : d112686 q = 1) : d142454 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109113, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109113, d142454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26230 q ha hb
  have h6 (q : Pattern) (ha : d109114 q = 1) (hb : d112686 q = 1) : d142455 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109114, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109114, d142455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109115 q = 1) (hb : d112686 q = 1) : d142456 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109115, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109115, d142456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109116 q = 1) (hb : d112686 q = 1) : d142457 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109116, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109116, d142457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109117 q = 1) (hb : d112686 q = 1) : d142458 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109117, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109117, d142458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109123 q = 1) (hb : d112686 q = 1) : d142464 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109123, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109123, d142464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26231 q ha hb
  have h11 (q : Pattern) (ha : d109124 q = 1) (hb : d112686 q = 1) : d142465 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109124, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109124, d142465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109125 q = 1) (hb : d112686 q = 1) : d142466 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109125, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109125, d142466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109126 q = 1) (hb : d112686 q = 1) : d142467 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109126, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109126, d142467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109127 q = 1) (hb : d112686 q = 1) : d142468 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109127, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109127, d142468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109128 q = 1) (hb : d112686 q = 1) : d142469 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109128, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109128, d142469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26233 (p : Pattern) (ha : d109134 p = 1) (hb : d112686 p = 1) : d142475 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d112686 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d109129 q = 1) (hb : d112686 q = 1) : d142470 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109129, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109129, d142470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26232 q ha hb
  have h3 (q : Pattern) (ha : d109130 q = 1) (hb : d112686 q = 1) : d142471 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109130, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109130, d142471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109131 q = 1) (hb : d112686 q = 1) : d142472 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109131, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109131, d142472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109132 q = 1) (hb : d112686 q = 1) : d142473 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109132, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109132, d142473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109133 q = 1) (hb : d112686 q = 1) : d142474 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109133, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d109133, d142474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d109134 q = 1) (hb : d112686 q = 1) : d142475 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109134, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109134, d142475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro26234 (p : Pattern) (ha : d109137 p = 1) (hb : d112686 p = 1) : d142478 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10890 q = 1) (hb : d112686 q = 1) : d141502 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d10890, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25780 q ha hb
    | true =>
      simp only [d10890, d141502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25781 q ha hb
  have h2 (q : Pattern) (ha : d10891 q = 1) (hb : d112686 q = 1) : d141503 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d10891, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10891, d141503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d10892 q = 1) (hb : d112686 q = 1) : d141504 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d10892, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10892, d141504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d10893 q = 1) (hb : d112686 q = 1) : d141505 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d10893, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10893, d141505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d10894 q = 1) (hb : d112686 q = 1) : d141506 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d10894, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d10894, d141506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109137 q = 1) (hb : d112686 q = 1) : d142478 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109137, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109137, d142478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26235 (p : Pattern) (ha : d109148 p = 1) (hb : d112686 p = 1) : d142489 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109143 q = 1) (hb : d112686 q = 1) : d142484 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109143, d142484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25808 q ha hb
    | true =>
      simp only [d109143, d142484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25787 q ha hb
  have h2 (q : Pattern) (ha : d109144 q = 1) (hb : d112686 q = 1) : d142485 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109144, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109144, d142485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109145 q = 1) (hb : d112686 q = 1) : d142486 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109145, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109145, d142486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109146 q = 1) (hb : d112686 q = 1) : d142487 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109146, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109146, d142487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109147 q = 1) (hb : d112686 q = 1) : d142488 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109147, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109147, d142488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109148 q = 1) (hb : d112686 q = 1) : d142489 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109148, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109148, d142489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26236 (p : Pattern) (ha : d109154 p = 1) (hb : d112686 p = 1) : d142495 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10896 q = 1) (hb : d112686 q = 1) : d141508 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d10896, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25779 q ha hb
    | true =>
      simp only [d10896, d141508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25782 q ha hb
  have h2 (q : Pattern) (ha : d10897 q = 1) (hb : d112686 q = 1) : d141509 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d10897, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10897, d141509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109135 q = 1) (hb : d112686 q = 1) : d142476 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109135, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109135, d142476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109136 q = 1) (hb : d112686 q = 1) : d142477 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109136, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109136, d142477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109138 q = 1) (hb : d112686 q = 1) : d142479 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109138, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109138, d142479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26234 q ha hb
  have h6 (q : Pattern) (ha : d109139 q = 1) (hb : d112686 q = 1) : d142480 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109139, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109139, d142480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109140 q = 1) (hb : d112686 q = 1) : d142481 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109140, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109140, d142481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109141 q = 1) (hb : d112686 q = 1) : d142482 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109141, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109141, d142482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109142 q = 1) (hb : d112686 q = 1) : d142483 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109142, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109142, d142483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109149 q = 1) (hb : d112686 q = 1) : d142490 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109149, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109149, d142490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26235 q ha hb
  have h11 (q : Pattern) (ha : d109150 q = 1) (hb : d112686 q = 1) : d142491 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109150, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109150, d142491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109151 q = 1) (hb : d112686 q = 1) : d142492 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109151, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109151, d142492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109152 q = 1) (hb : d112686 q = 1) : d142493 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109152, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109152, d142493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109153 q = 1) (hb : d112686 q = 1) : d142494 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109153, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109153, d142494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109154 q = 1) (hb : d112686 q = 1) : d142495 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109154, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109154, d142495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26237 (p : Pattern) (ha : d109160 p = 1) (hb : d112686 p = 1) : d142501 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109155 q = 1) (hb : d112686 q = 1) : d142496 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109155, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109155, d142496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26236 q ha hb
  have h2 (q : Pattern) (ha : d109156 q = 1) (hb : d112686 q = 1) : d142497 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109156, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109156, d142497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109157 q = 1) (hb : d112686 q = 1) : d142498 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109157, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109157, d142498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109158 q = 1) (hb : d112686 q = 1) : d142499 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109158, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109158, d142499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109159 q = 1) (hb : d112686 q = 1) : d142500 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109159, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109159, d142500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109160 q = 1) (hb : d112686 q = 1) : d142501 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109160, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109160, d142501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26238 (p : Pattern) (ha : d109164 p = 1) (hb : d112686 p = 1) : d142505 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11130 q = 1) (hb : d112686 q = 1) : d141681 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11130, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25818 q ha hb
    | true =>
      simp only [d11130, d141681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25819 q ha hb
  have h2 (q : Pattern) (ha : d11131 q = 1) (hb : d112686 q = 1) : d141682 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11131, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11131, d141682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11132 q = 1) (hb : d112686 q = 1) : d141683 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11132, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11132, d141683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11133 q = 1) (hb : d112686 q = 1) : d141684 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11133, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11133, d141684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11134 q = 1) (hb : d112686 q = 1) : d141685 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11134, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11134, d141685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109164 q = 1) (hb : d112686 q = 1) : d142505 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109164, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109164, d142505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26239 (p : Pattern) (ha : d109175 p = 1) (hb : d112686 p = 1) : d142516 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109170 q = 1) (hb : d112686 q = 1) : d142511 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109170, d142511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25848 q ha hb
    | true =>
      simp only [d109170, d142511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25825 q ha hb
  have h2 (q : Pattern) (ha : d109171 q = 1) (hb : d112686 q = 1) : d142512 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109171, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109171, d142512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109172 q = 1) (hb : d112686 q = 1) : d142513 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109172, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109172, d142513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109173 q = 1) (hb : d112686 q = 1) : d142514 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109173, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109173, d142514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109174 q = 1) (hb : d112686 q = 1) : d142515 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109174, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109174, d142515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109175 q = 1) (hb : d112686 q = 1) : d142516 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109175, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109175, d142516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26240 (p : Pattern) (ha : d109181 p = 1) (hb : d112686 p = 1) : d142522 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11136 q = 1) (hb : d112686 q = 1) : d141687 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11136, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25817 q ha hb
    | true =>
      simp only [d11136, d141687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25820 q ha hb
  have h2 (q : Pattern) (ha : d11137 q = 1) (hb : d112686 q = 1) : d141688 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11137, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11137, d141688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109162 q = 1) (hb : d112686 q = 1) : d142503 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109162, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109162, d142503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109163 q = 1) (hb : d112686 q = 1) : d142504 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109163, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109163, d142504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109165 q = 1) (hb : d112686 q = 1) : d142506 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109165, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109165, d142506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26238 q ha hb
  have h6 (q : Pattern) (ha : d109166 q = 1) (hb : d112686 q = 1) : d142507 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109166, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109166, d142507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109167 q = 1) (hb : d112686 q = 1) : d142508 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109167, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109167, d142508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109168 q = 1) (hb : d112686 q = 1) : d142509 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109168, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109168, d142509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109169 q = 1) (hb : d112686 q = 1) : d142510 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109169, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109169, d142510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109176 q = 1) (hb : d112686 q = 1) : d142517 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109176, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109176, d142517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26239 q ha hb
  have h11 (q : Pattern) (ha : d109177 q = 1) (hb : d112686 q = 1) : d142518 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109177, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109177, d142518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109178 q = 1) (hb : d112686 q = 1) : d142519 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109178, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109178, d142519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109179 q = 1) (hb : d112686 q = 1) : d142520 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109179, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109179, d142520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109180 q = 1) (hb : d112686 q = 1) : d142521 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109180, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109180, d142521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109181 q = 1) (hb : d112686 q = 1) : d142522 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109181, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109181, d142522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26241 (p : Pattern) (ha : d109187 p = 1) (hb : d112686 p = 1) : d142528 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109182 q = 1) (hb : d112686 q = 1) : d142523 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109182, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109182, d142523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26240 q ha hb
  have h2 (q : Pattern) (ha : d109183 q = 1) (hb : d112686 q = 1) : d142524 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109183, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109183, d142524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109184 q = 1) (hb : d112686 q = 1) : d142525 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109184, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109184, d142525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109185 q = 1) (hb : d112686 q = 1) : d142526 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109185, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109185, d142526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109186 q = 1) (hb : d112686 q = 1) : d142527 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109186, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109186, d142527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109187 q = 1) (hb : d112686 q = 1) : d142528 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109187, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109187, d142528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26242 (p : Pattern) (ha : d109192 p = 1) (hb : d112686 p = 1) : d142533 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11400 q = 1) (hb : d112686 q = 1) : d141868 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11400, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25860 q ha hb
    | true =>
      simp only [d11400, d141868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25861 q ha hb
  have h2 (q : Pattern) (ha : d11401 q = 1) (hb : d112686 q = 1) : d141869 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11401, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11401, d141869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11402 q = 1) (hb : d112686 q = 1) : d141870 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11402, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11402, d141870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11403 q = 1) (hb : d112686 q = 1) : d141871 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11403, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11403, d141871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11404 q = 1) (hb : d112686 q = 1) : d141872 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11404, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11404, d141872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109192 q = 1) (hb : d112686 q = 1) : d142533 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109192, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109192, d142533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26243 (p : Pattern) (ha : d109203 p = 1) (hb : d112686 p = 1) : d142544 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109198 q = 1) (hb : d112686 q = 1) : d142539 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109198, d142539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25890 q ha hb
    | true =>
      simp only [d109198, d142539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25867 q ha hb
  have h2 (q : Pattern) (ha : d109199 q = 1) (hb : d112686 q = 1) : d142540 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109199, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109199, d142540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109200 q = 1) (hb : d112686 q = 1) : d142541 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109200, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109200, d142541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109201 q = 1) (hb : d112686 q = 1) : d142542 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109201, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109201, d142542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109202 q = 1) (hb : d112686 q = 1) : d142543 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109202, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109202, d142543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109203 q = 1) (hb : d112686 q = 1) : d142544 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109203, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109203, d142544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26244 (p : Pattern) (ha : d109209 p = 1) (hb : d112686 p = 1) : d142550 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11406 q = 1) (hb : d112686 q = 1) : d141874 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11406, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25859 q ha hb
    | true =>
      simp only [d11406, d141874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25862 q ha hb
  have h2 (q : Pattern) (ha : d11407 q = 1) (hb : d112686 q = 1) : d141875 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11407, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11407, d141875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109190 q = 1) (hb : d112686 q = 1) : d142531 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109190, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109190, d142531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109191 q = 1) (hb : d112686 q = 1) : d142532 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109191, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109191, d142532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109193 q = 1) (hb : d112686 q = 1) : d142534 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109193, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109193, d142534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26242 q ha hb
  have h6 (q : Pattern) (ha : d109194 q = 1) (hb : d112686 q = 1) : d142535 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109194, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109194, d142535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109195 q = 1) (hb : d112686 q = 1) : d142536 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109195, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109195, d142536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109196 q = 1) (hb : d112686 q = 1) : d142537 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109196, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109196, d142537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109197 q = 1) (hb : d112686 q = 1) : d142538 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109197, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109197, d142538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109204 q = 1) (hb : d112686 q = 1) : d142545 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109204, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109204, d142545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26243 q ha hb
  have h11 (q : Pattern) (ha : d109205 q = 1) (hb : d112686 q = 1) : d142546 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109205, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109205, d142546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109206 q = 1) (hb : d112686 q = 1) : d142547 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109206, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109206, d142547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109207 q = 1) (hb : d112686 q = 1) : d142548 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109207, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109207, d142548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109208 q = 1) (hb : d112686 q = 1) : d142549 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109208, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109208, d142549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109209 q = 1) (hb : d112686 q = 1) : d142550 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109209, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109209, d142550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26245 (p : Pattern) (ha : d109215 p = 1) (hb : d112686 p = 1) : d142556 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109210 q = 1) (hb : d112686 q = 1) : d142551 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109210, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109210, d142551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26244 q ha hb
  have h2 (q : Pattern) (ha : d109211 q = 1) (hb : d112686 q = 1) : d142552 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109211, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109211, d142552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109212 q = 1) (hb : d112686 q = 1) : d142553 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109212, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109212, d142553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109213 q = 1) (hb : d112686 q = 1) : d142554 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109213, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109213, d142554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109214 q = 1) (hb : d112686 q = 1) : d142555 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109214, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109214, d142555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109215 q = 1) (hb : d112686 q = 1) : d142556 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109215, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109215, d142556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26246 (p : Pattern) (ha : d109221 p = 1) (hb : d112686 p = 1) : d142562 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11671 q = 1) (hb : d112686 q = 1) : d142056 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d11671, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25902 q ha hb
    | true =>
      simp only [d11671, d142056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25903 q ha hb
  have h2 (q : Pattern) (ha : d11672 q = 1) (hb : d112686 q = 1) : d142057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d11672, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11672, d142057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d11673 q = 1) (hb : d112686 q = 1) : d142058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d11673, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d11673, d142058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d11674 q = 1) (hb : d112686 q = 1) : d142059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d11674, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11674, d142059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d11675 q = 1) (hb : d112686 q = 1) : d142060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d11675, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d11675, d142060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109221 q = 1) (hb : d112686 q = 1) : d142562 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109221, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109221, d142562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26247 (p : Pattern) (ha : d109232 p = 1) (hb : d112686 p = 1) : d142573 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109227 q = 1) (hb : d112686 q = 1) : d142568 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d109227, d142568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25932 q ha hb
    | true =>
      simp only [d109227, d142568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25909 q ha hb
  have h2 (q : Pattern) (ha : d109228 q = 1) (hb : d112686 q = 1) : d142569 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d109228, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109228, d142569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109229 q = 1) (hb : d112686 q = 1) : d142570 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d109229, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109229, d142570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109230 q = 1) (hb : d112686 q = 1) : d142571 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d109230, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109230, d142571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109231 q = 1) (hb : d112686 q = 1) : d142572 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d109231, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109231, d142572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109232 q = 1) (hb : d112686 q = 1) : d142573 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d109232, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109232, d142573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro26248 (p : Pattern) (ha : d109238 p = 1) (hb : d112686 p = 1) : d142579 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d11677 q = 1) (hb : d112686 q = 1) : d142062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d11677, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25901 q ha hb
    | true =>
      simp only [d11677, d142062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro25904 q ha hb
  have h2 (q : Pattern) (ha : d11678 q = 1) (hb : d112686 q = 1) : d142063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d11678, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d11678, d142063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d109219 q = 1) (hb : d112686 q = 1) : d142560 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109219, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d109219, d142560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d109220 q = 1) (hb : d112686 q = 1) : d142561 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109220, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109220, d142561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109222 q = 1) (hb : d112686 q = 1) : d142563 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109222, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109222, d142563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26246 q ha hb
  have h6 (q : Pattern) (ha : d109223 q = 1) (hb : d112686 q = 1) : d142564 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109223, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d109223, d142564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d109224 q = 1) (hb : d112686 q = 1) : d142565 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109224, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d109224, d142565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d109225 q = 1) (hb : d112686 q = 1) : d142566 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109225, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d109225, d142566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d109226 q = 1) (hb : d112686 q = 1) : d142567 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109226, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d109226, d142567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d109233 q = 1) (hb : d112686 q = 1) : d142574 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d109233, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109233, d142574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26247 q ha hb
  have h11 (q : Pattern) (ha : d109234 q = 1) (hb : d112686 q = 1) : d142575 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d109234, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d109234, d142575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d109235 q = 1) (hb : d112686 q = 1) : d142576 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d109235, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d109235, d142576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d109236 q = 1) (hb : d112686 q = 1) : d142577 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d109236, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d109236, d142577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d109237 q = 1) (hb : d112686 q = 1) : d142578 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d109237, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d109237, d142578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d109238 q = 1) (hb : d112686 q = 1) : d142579 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d109238, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d109238, d142579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro26249 (p : Pattern) (ha : d109244 p = 1) (hb : d112686 p = 1) : d142585 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d112686 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d109239 q = 1) (hb : d112686 q = 1) : d142580 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d109239, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109239, d142580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro26248 q ha hb
  have h2 (q : Pattern) (ha : d109240 q = 1) (hb : d112686 q = 1) : d142581 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d109240, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109240, d142581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d109241 q = 1) (hb : d112686 q = 1) : d142582 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d109241, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109241, d142582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d109242 q = 1) (hb : d112686 q = 1) : d142583 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d109242, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109242, d142583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d109243 q = 1) (hb : d112686 q = 1) : d142584 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d109243, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109243, d142584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d109244 q = 1) (hb : d112686 q = 1) : d142585 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d109244, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d109244, d142585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
