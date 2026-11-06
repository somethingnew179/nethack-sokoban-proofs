import NetHack.Soko22Hazard87.AndIntroBlocks0148
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro37250 (p : Pattern) (ha : d147527 p = 1) (hb : d170011 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21742 q = 1) (hb : d147508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d147508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28193 q ha hb
    | true =>
      simp only [d21742, d147508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21743 q = 1) (hb : d147509 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d147509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21743, d147509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21744 q = 1) (hb : d147510 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21744, d147510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21744, d147510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21745 q = 1) (hb : d147511 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21745, d147511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21745, d147511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147524 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147525 q = 1) (hb : d170010 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147525, d170010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147525, d170010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13027 q = 1) (hb : d113357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13028 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21760 q = 1) (hb : d147526 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21760, d147526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21760, d147526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d147527 q = 1) (hb : d170011 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147527, d170011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147527, d170011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37251 (p : Pattern) (ha : d147549 p = 1) (hb : d170024 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147528 q = 1) (hb : d170012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147528, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37249 q ha hb
    | true =>
      simp only [d147528, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
  have h2 (q : Pattern) (ha : d147529 q = 1) (hb : d170013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147529, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147529, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147530 q = 1) (hb : d170014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147530, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147530, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147538 q = 1) (hb : d170015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147538, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
    | true =>
      simp only [d147538, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37246 q hb ha
  have h5 (q : Pattern) (ha : d147539 q = 1) (hb : d170016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147539, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147539, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147540 q = 1) (hb : d170017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147540, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147540, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147541 q = 1) (hb : d170018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147541, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147541, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147544 q = 1) (hb : d170019 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147544, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
    | true =>
      simp only [d147544, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37247 q hb ha
  have h9 (q : Pattern) (ha : d147545 q = 1) (hb : d170020 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147545, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147545, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147546 q = 1) (hb : d170021 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147546, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147546, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147547 q = 1) (hb : d170022 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147547, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147547, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147548 q = 1) (hb : d170023 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147548, d170023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147548, d170023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147549 q = 1) (hb : d170024 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147549, d170024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147549, d170024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37252 (p : Pattern) (ha : d147553 p = 1) (hb : d170028 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147544 q = 1) (hb : d170019 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147544, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
    | true =>
      simp only [d147544, d170019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37247 q hb ha
  have h2 (q : Pattern) (ha : d147545 q = 1) (hb : d170020 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147545, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147545, d170020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147546 q = 1) (hb : d170021 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147546, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147546, d170021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147547 q = 1) (hb : d170022 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147547, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147547, d170022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147552 q = 1) (hb : d170027 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147552, d170027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147552, d170027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147553 q = 1) (hb : d170028 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147553, d170028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147553, d170028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37253 (p : Pattern) (ha : d147559 p = 1) (hb : d170034 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37251 q ha hb
    | true =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147557 q = 1) (hb : d170032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147557, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147557, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147558 q = 1) (hb : d170033 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147558, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147558, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147559 q = 1) (hb : d170034 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147559, d170034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147559, d170034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37254 (p : Pattern) (ha : d147563 p = 1) (hb : d170038 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147561 q = 1) (hb : d170036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147561, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147561, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147562 q = 1) (hb : d170037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147562, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147562, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147563 q = 1) (hb : d170038 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147563, d170038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147563, d170038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37255 (p : Pattern) (ha : d147569 p = 1) (hb : d170044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147564 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37253 q ha hb
    | true =>
      simp only [d147564, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37254 q ha hb
  have h2 (q : Pattern) (ha : d147565 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147565, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147565, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147566 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147566, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147566, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147567 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147567, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147567, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147568 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147568, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147568, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147569 q = 1) (hb : d170044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147569, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147569, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37256 (p : Pattern) (ha : d147572 p = 1) (hb : d170047 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37251 q ha hb
    | true =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147557 q = 1) (hb : d170032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147557, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147557, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147558 q = 1) (hb : d170033 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147558, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147558, d170033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147572 q = 1) (hb : d170047 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147572, d170047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147572, d170047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37257 (p : Pattern) (ha : d147573 p = 1) (hb : d170048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147561 q = 1) (hb : d170036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147561, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147561, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147562 q = 1) (hb : d170037 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147562, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147562, d170037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147573 q = 1) (hb : d170048 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147573, d170048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147573, d170048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37258 (p : Pattern) (ha : d147579 p = 1) (hb : d170054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147564 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37253 q ha hb
    | true =>
      simp only [d147564, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37254 q ha hb
  have h2 (q : Pattern) (ha : d147565 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147565, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147565, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147566 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147566, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147566, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147567 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147567, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147567, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147568 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147568, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147568, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147574 q = 1) (hb : d170049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37256 q ha hb
    | true =>
      simp only [d147574, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37257 q ha hb
  have h7 (q : Pattern) (ha : d147575 q = 1) (hb : d170050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147575, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147575, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147576 q = 1) (hb : d170051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147576, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147576, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147577 q = 1) (hb : d170052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147577, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147577, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147578 q = 1) (hb : d170053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147578, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147578, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147579 q = 1) (hb : d170054 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147579, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147579, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37259 (p : Pattern) (ha : d147584 p = 1) (hb : d170059 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37251 q ha hb
    | true =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147557 q = 1) (hb : d170032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147557, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147557, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147583 q = 1) (hb : d170058 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147583, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147583, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147584 q = 1) (hb : d170059 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147584, d170059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147584, d170059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37260 (p : Pattern) (ha : d147586 p = 1) (hb : d170061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147561 q = 1) (hb : d170036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147561, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147561, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147585 q = 1) (hb : d170060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147585, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147585, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147586 q = 1) (hb : d170061 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147586, d170061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147586, d170061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37261 (p : Pattern) (ha : d147593 p = 1) (hb : d170068 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37251 q ha hb
    | true =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147591 q = 1) (hb : d170066 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147591, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147591, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147592 q = 1) (hb : d170067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147592, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147592, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147593 q = 1) (hb : d170068 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147593, d170068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147593, d170068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37262 (p : Pattern) (ha : d147596 p = 1) (hb : d170071 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147594 q = 1) (hb : d170069 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147594, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147594, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147595 q = 1) (hb : d170070 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147595, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147595, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147596 q = 1) (hb : d170071 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147596, d170071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147596, d170071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37263 (p : Pattern) (ha : d21840 p = 1) (hb : d147606 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d822 q = 1) (hb : d52499 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro120 q ha hb
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d823 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d9759 q = 1) (hb : d101280 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9759, d101280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d9759, d101280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d9760 q = 1) (hb : d101281 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9760, d101281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9760, d101281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d9761 q = 1) (hb : d101282 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9761, d101282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d9761, d101282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d21840 q = 1) (hb : d147606 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d21840, d147606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d21840, d147606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37264 (p : Pattern) (ha : d147612 p = 1) (hb : d170077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21835 q = 1) (hb : d147601 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21835, d147601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28209 q ha hb
    | true =>
      simp only [d21835, d147601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21836 q = 1) (hb : d147602 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21836, d147602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21836, d147602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21837 q = 1) (hb : d147603 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21837, d147603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21837, d147603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21838 q = 1) (hb : d147604 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21838, d147604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21838, d147604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147506 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147605 q = 1) (hb : d170075 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147605, d170075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147605, d170075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d21841 q = 1) (hb : d147607 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21841, d147607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37263 q ha hb
    | true =>
      simp only [d21841, d147607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d21842 q = 1) (hb : d147608 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21842, d147608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d21842, d147608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d21843 q = 1) (hb : d147609 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21843, d147609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21843, d147609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d21844 q = 1) (hb : d147610 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21844, d147610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d21844, d147610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147517 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147611 q = 1) (hb : d170076 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147611, d170076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147611, d170076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d147612 q = 1) (hb : d170077 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147612, d170077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147612, d170077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro37265 (p : Pattern) (ha : d147622 p = 1) (hb : d170082 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d21851 q = 1) (hb : d147617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21851, d147617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29766 q ha hb
    | true =>
      simp only [d21851, d147617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d21852 q = 1) (hb : d147618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21852, d147618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d21852, d147618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d21853 q = 1) (hb : d147619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d21853, d147619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d21853, d147619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21854 q = 1) (hb : d147620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d21854, d147620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d21854, d147620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147621 q = 1) (hb : d170081 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147621, d170081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147621, d170081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13027 q = 1) (hb : d113357 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13027, d113357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13028 q = 1) (hb : d113358 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13028, d113358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d21760 q = 1) (hb : d147526 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d21760, d147526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21760, d147526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d147622 q = 1) (hb : d170082 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147622, d170082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147622, d170082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37266 (p : Pattern) (ha : d147628 p = 1) (hb : d170088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147613 q = 1) (hb : d170078 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147613, d170078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37264 q ha hb
    | true =>
      simp only [d147613, d170078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37249 q ha hb
  have h2 (q : Pattern) (ha : d147614 q = 1) (hb : d170079 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147614, d170079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147614, d170079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147615 q = 1) (hb : d170080 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147615, d170080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147615, d170080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147623 q = 1) (hb : d170083 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147623, d170083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37249 q ha hb
    | true =>
      simp only [d147623, d170083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37265 q ha hb
  have h5 (q : Pattern) (ha : d147624 q = 1) (hb : d170084 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147624, d170084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147624, d170084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147625 q = 1) (hb : d170085 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147625, d170085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147625, d170085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147626 q = 1) (hb : d170086 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147626, d170086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147626, d170086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147528 q = 1) (hb : d170012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147528, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37249 q ha hb
    | true =>
      simp only [d147528, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
  have h9 (q : Pattern) (ha : d147529 q = 1) (hb : d170013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147529, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147529, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147530 q = 1) (hb : d170014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147530, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147530, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147538 q = 1) (hb : d170015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147538, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
    | true =>
      simp only [d147538, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37246 q hb ha
  have h12 (q : Pattern) (ha : d147539 q = 1) (hb : d170016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147539, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147539, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147540 q = 1) (hb : d170017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147540, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147540, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147541 q = 1) (hb : d170018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147541, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147541, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147627 q = 1) (hb : d170087 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147627, d170087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147627, d170087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147628 q = 1) (hb : d170088 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147628, d170088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147628, d170088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro37267 (p : Pattern) (ha : d147633 p = 1) (hb : d170093 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147528 q = 1) (hb : d170012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147528, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37249 q ha hb
    | true =>
      simp only [d147528, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
  have h2 (q : Pattern) (ha : d147529 q = 1) (hb : d170013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147529, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147529, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147530 q = 1) (hb : d170014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147530, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147530, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147538 q = 1) (hb : d170015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147538, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
    | true =>
      simp only [d147538, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37246 q hb ha
  have h5 (q : Pattern) (ha : d147539 q = 1) (hb : d170016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147539, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147539, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147540 q = 1) (hb : d170017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147540, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147540, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147541 q = 1) (hb : d170018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147541, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147541, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147631 q = 1) (hb : d170091 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147631, d170091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147631, d170091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147632 q = 1) (hb : d170092 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147632, d170092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147632, d170092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147633 q = 1) (hb : d170093 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147633, d170093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147633, d170093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37268 (p : Pattern) (ha : d147639 p = 1) (hb : d170099 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147629 q = 1) (hb : d170089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147629, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37266 q ha hb
    | true =>
      simp only [d147629, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147630 q = 1) (hb : d170090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147630, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147630, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147634 q = 1) (hb : d170094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147634, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37267 q ha hb
    | true =>
      simp only [d147634, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147635 q = 1) (hb : d170095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147635, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147635, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147636 q = 1) (hb : d170096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147636, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147636, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147637 q = 1) (hb : d170097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147637, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147637, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147638 q = 1) (hb : d170098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147638, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147638, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147639 q = 1) (hb : d170099 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147639, d170099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147639, d170099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37269 (p : Pattern) (ha : d147643 p = 1) (hb : d170103 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147634 q = 1) (hb : d170094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147634, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37267 q ha hb
    | true =>
      simp only [d147634, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147635 q = 1) (hb : d170095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147635, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147635, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147640 q = 1) (hb : d170100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147640, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147640, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147641 q = 1) (hb : d170101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147641, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147641, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147642 q = 1) (hb : d170102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147642, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147642, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147643 q = 1) (hb : d170103 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147643, d170103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147643, d170103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37270 (p : Pattern) (ha : d147652 p = 1) (hb : d170111 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147528 q = 1) (hb : d170012 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147528, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37249 q ha hb
    | true =>
      simp only [d147528, d170012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
  have h2 (q : Pattern) (ha : d147529 q = 1) (hb : d170013 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147529, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147529, d170013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147530 q = 1) (hb : d170014 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147530, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147530, d170014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147538 q = 1) (hb : d170015 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147538, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
    | true =>
      simp only [d147538, d170015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37246 q hb ha
  have h5 (q : Pattern) (ha : d147539 q = 1) (hb : d170016 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147539, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147539, d170016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147540 q = 1) (hb : d170017 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147540, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147540, d170017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147541 q = 1) (hb : d170018 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147541, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147541, d170018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147647 q = 1) (hb : d170106 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147647, d170106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37250 q ha hb
    | true =>
      simp only [d147647, d170106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29772 q hb ha
  have h9 (q : Pattern) (ha : d147648 q = 1) (hb : d170107 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147648, d170107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147648, d170107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147649 q = 1) (hb : d170108 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147649, d170108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147649, d170108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147650 q = 1) (hb : d170109 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147650, d170109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147650, d170109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147651 q = 1) (hb : d170110 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147651, d170110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147651, d170110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147652 q = 1) (hb : d170111 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147652, d170111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147652, d170111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37271 (p : Pattern) (ha : d147658 p = 1) (hb : d170117 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147653 q = 1) (hb : d170112 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147653, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37270 q ha hb
    | true =>
      simp only [d147653, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147654 q = 1) (hb : d170113 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147654, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147654, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147655 q = 1) (hb : d170114 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147655, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147655, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147656 q = 1) (hb : d170115 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147656, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147656, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147657 q = 1) (hb : d170116 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147657, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147657, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147658 q = 1) (hb : d170117 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147658, d170117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147658, d170117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37272 (p : Pattern) (ha : d147664 p = 1) (hb : d170123 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147587 q = 1) (hb : d170062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147587, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37259 q ha hb
    | true =>
      simp only [d147587, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37260 q ha hb
  have h2 (q : Pattern) (ha : d147588 q = 1) (hb : d170063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147588, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147588, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147589 q = 1) (hb : d170064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147589, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147589, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147590 q = 1) (hb : d170065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147590, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147590, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147597 q = 1) (hb : d170072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147597, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37261 q ha hb
    | true =>
      simp only [d147597, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37262 q ha hb
  have h6 (q : Pattern) (ha : d147598 q = 1) (hb : d170073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147598, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147598, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147599 q = 1) (hb : d170074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147599, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147599, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147644 q = 1) (hb : d170104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147644, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37268 q ha hb
    | true =>
      simp only [d147644, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37269 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147564 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147645 q = 1) (hb : d170105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147645, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147659 q = 1) (hb : d170118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147659, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37271 q ha hb
    | true =>
      simp only [d147659, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147660 q = 1) (hb : d170119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147660, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147660, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147661 q = 1) (hb : d170120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147661, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147662 q = 1) (hb : d170121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147662, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147663 q = 1) (hb : d170122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147663, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147664 q = 1) (hb : d170123 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147664, d170123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147664, d170123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37273 (p : Pattern) (ha : d147665 p = 1) (hb : d170124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37251 q ha hb
    | true =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147557 q = 1) (hb : d170032 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147557, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147557, d170032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147583 q = 1) (hb : d170058 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147583, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147583, d170058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147665 q = 1) (hb : d170124 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147665, d170124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147665, d170124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37274 (p : Pattern) (ha : d147666 p = 1) (hb : d170125 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147561 q = 1) (hb : d170036 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147561, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147561, d170036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147585 q = 1) (hb : d170060 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147585, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147585, d170060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147666 q = 1) (hb : d170125 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147666, d170125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147666, d170125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37275 (p : Pattern) (ha : d147671 p = 1) (hb : d170130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147550 q = 1) (hb : d170025 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37251 q ha hb
    | true =>
      simp only [d147550, d170025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147551 q = 1) (hb : d170026 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147551, d170026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147556 q = 1) (hb : d170031 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147556, d170031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147591 q = 1) (hb : d170066 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147591, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147591, d170066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147592 q = 1) (hb : d170067 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147592, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147592, d170067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147671 q = 1) (hb : d170130 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147671, d170130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147671, d170130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37276 (p : Pattern) (ha : d147672 p = 1) (hb : d170131 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147560 q = 1) (hb : d170035 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147560, d170035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147594 q = 1) (hb : d170069 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147594, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147594, d170069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147595 q = 1) (hb : d170070 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147595, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147595, d170070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147672 q = 1) (hb : d170131 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147672, d170131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147672, d170131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37277 (p : Pattern) (ha : d147676 p = 1) (hb : d170135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147629 q = 1) (hb : d170089 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147629, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37266 q ha hb
    | true =>
      simp only [d147629, d170089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147630 q = 1) (hb : d170090 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147630, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147630, d170090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147634 q = 1) (hb : d170094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147634, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37267 q ha hb
    | true =>
      simp only [d147634, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147635 q = 1) (hb : d170095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147635, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147635, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147636 q = 1) (hb : d170096 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147636, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147636, d170096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147637 q = 1) (hb : d170097 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147637, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147637, d170097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147638 q = 1) (hb : d170098 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147638, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147638, d170098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147676 q = 1) (hb : d170135 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147676, d170135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147676, d170135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37278 (p : Pattern) (ha : d147677 p = 1) (hb : d170136 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147634 q = 1) (hb : d170094 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147634, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37267 q ha hb
    | true =>
      simp only [d147634, d170094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147635 q = 1) (hb : d170095 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147635, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147635, d170095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147554 q = 1) (hb : d170029 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37252 q ha hb
    | true =>
      simp only [d147554, d170029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147555 q = 1) (hb : d170030 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147555, d170030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147640 q = 1) (hb : d170100 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147640, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147640, d170100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147641 q = 1) (hb : d170101 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147641, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147641, d170101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147642 q = 1) (hb : d170102 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147642, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147642, d170102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147677 q = 1) (hb : d170136 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147677, d170136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147677, d170136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37279 (p : Pattern) (ha : d147680 p = 1) (hb : d170139 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147653 q = 1) (hb : d170112 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147653, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37270 q ha hb
    | true =>
      simp only [d147653, d170112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147654 q = 1) (hb : d170113 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147654, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147654, d170113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147655 q = 1) (hb : d170114 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147655, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147655, d170114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147656 q = 1) (hb : d170115 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147656, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147656, d170115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147657 q = 1) (hb : d170116 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147657, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147657, d170116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147680 q = 1) (hb : d170139 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147680, d170139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147680, d170139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37280 (p : Pattern) (ha : d147686 p = 1) (hb : d170145 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147587 q = 1) (hb : d170062 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147587, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37259 q ha hb
    | true =>
      simp only [d147587, d170062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37260 q ha hb
  have h2 (q : Pattern) (ha : d147588 q = 1) (hb : d170063 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147588, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147588, d170063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147589 q = 1) (hb : d170064 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147589, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147589, d170064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147590 q = 1) (hb : d170065 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147590, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147590, d170065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147597 q = 1) (hb : d170072 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147597, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37261 q ha hb
    | true =>
      simp only [d147597, d170072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37262 q ha hb
  have h6 (q : Pattern) (ha : d147598 q = 1) (hb : d170073 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147598, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147598, d170073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147599 q = 1) (hb : d170074 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147599, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147599, d170074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147644 q = 1) (hb : d170104 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147644, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37268 q ha hb
    | true =>
      simp only [d147644, d170104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37269 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147564 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147645 q = 1) (hb : d170105 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147645, d170105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d147659 q = 1) (hb : d170118 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147659, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37271 q ha hb
    | true =>
      simp only [d147659, d170118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147660 q = 1) (hb : d170119 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147660, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147660, d170119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d147661 q = 1) (hb : d170120 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147661, d170120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147662 q = 1) (hb : d170121 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147662, d170121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147663 q = 1) (hb : d170122 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147663, d170122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147667 q = 1) (hb : d170126 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147667, d170126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37273 q ha hb
    | true =>
      simp only [d147667, d170126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37274 q ha hb
  have h17 (q : Pattern) (ha : d147668 q = 1) (hb : d170127 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147668, d170127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147668, d170127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147669 q = 1) (hb : d170128 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147669, d170128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147669, d170128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d147670 q = 1) (hb : d170129 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147670, d170129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147670, d170129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147673 q = 1) (hb : d170132 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147673, d170132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37275 q ha hb
    | true =>
      simp only [d147673, d170132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37276 q ha hb
  have h21 (q : Pattern) (ha : d147674 q = 1) (hb : d170133 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147674, d170133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147674, d170133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d147675 q = 1) (hb : d170134 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147675, d170134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147675, d170134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147678 q = 1) (hb : d170137 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147678, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37277 q ha hb
    | true =>
      simp only [d147678, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37278 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147574 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d147679 q = 1) (hb : d170138 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d147679, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d147681 q = 1) (hb : d170140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147681, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37279 q ha hb
    | true =>
      simp only [d147681, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d147682 q = 1) (hb : d170141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147682, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d147682, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d147683 q = 1) (hb : d170142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d147683, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d147684 q = 1) (hb : d170143 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147684, d170143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d147684, d170143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d147685 q = 1) (hb : d170144 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147685, d170144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147685, d170144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d147686 q = 1) (hb : d170145 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147686, d170145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147686, d170145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro37281 (p : Pattern) (ha : d147698 p = 1) (hb : d170157 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147688 q = 1) (hb : d170147 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147688, d170147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37269 q ha hb
    | true =>
      simp only [d147688, d170147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37254 q ha hb
  have h2 (q : Pattern) (ha : d147689 q = 1) (hb : d170148 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147689, d170148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147689, d170148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147690 q = 1) (hb : d170149 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147690, d170149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147690, d170149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147691 q = 1) (hb : d170150 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147691, d170150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147691, d170150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147692 q = 1) (hb : d170151 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147692, d170151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147692, d170151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147693 q = 1) (hb : d170152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147693, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37254 q ha hb
    | true =>
      simp only [d147693, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147694 q = 1) (hb : d170153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147694, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147694, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147695 q = 1) (hb : d170154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147695, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147695, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147696 q = 1) (hb : d170155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147696, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147696, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147697 q = 1) (hb : d170156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147697, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147697, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147698 q = 1) (hb : d170157 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147698, d170157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147698, d170157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37282 (p : Pattern) (ha : d147704 p = 1) (hb : d170163 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147693 q = 1) (hb : d170152 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147693, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37254 q ha hb
    | true =>
      simp only [d147693, d170152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147694 q = 1) (hb : d170153 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147694, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147694, d170153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147695 q = 1) (hb : d170154 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147695, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147695, d170154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147696 q = 1) (hb : d170155 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147696, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147696, d170155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147697 q = 1) (hb : d170156 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147697, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147697, d170156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147699 q = 1) (hb : d170158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147699, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37257 q ha hb
    | true =>
      simp only [d147699, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147700 q = 1) (hb : d170159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147700, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147700, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147701 q = 1) (hb : d170160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147701, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147701, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147702 q = 1) (hb : d170161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147702, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147702, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147703 q = 1) (hb : d170162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147703, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147703, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147704 q = 1) (hb : d170163 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147704, d170163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147704, d170163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37283 (p : Pattern) (ha : d147711 p = 1) (hb : d170170 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147678 q = 1) (hb : d170137 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147678, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37277 q ha hb
    | true =>
      simp only [d147678, d170137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37278 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147574 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147679 q = 1) (hb : d170138 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147679, d170138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147681 q = 1) (hb : d170140 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147681, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37279 q ha hb
    | true =>
      simp only [d147681, d170140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147682 q = 1) (hb : d170141 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147682, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147682, d170141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147683 q = 1) (hb : d170142 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147683, d170142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147709 q = 1) (hb : d170168 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147709, d170168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147709, d170168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147710 q = 1) (hb : d170169 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147710, d170169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147710, d170169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147711 q = 1) (hb : d170170 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147711, d170170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147711, d170170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37284 (p : Pattern) (ha : d147713 p = 1) (hb : d170172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147699 q = 1) (hb : d170158 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147699, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37257 q ha hb
    | true =>
      simp only [d147699, d170158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147700 q = 1) (hb : d170159 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147700, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147700, d170159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147701 q = 1) (hb : d170160 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147701, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147701, d170160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147702 q = 1) (hb : d170161 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147702, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147702, d170161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147703 q = 1) (hb : d170162 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147703, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147703, d170162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147713 q = 1) (hb : d170172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147713, d170172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147713, d170172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37285 (p : Pattern) (ha : d22078 p = 1) (hb : d147773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22073 q = 1) (hb : d147768 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22073, d147768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22073, d147768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29751 q ha hb
  have h2 (q : Pattern) (ha : d21766 q = 1) (hb : d147532 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21766, d147532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29751 q ha hb
    | true =>
      simp only [d21766, d147532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22074 q = 1) (hb : d147769 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22074, d147769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22074, d147769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21767 q = 1) (hb : d147533 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21767, d147533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21767, d147533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22075 q = 1) (hb : d147770 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22075, d147770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22075, d147770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22076 q = 1) (hb : d147771 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22076, d147771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22076, d147771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22077 q = 1) (hb : d147772 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22077, d147772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22077, d147772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22078 q = 1) (hb : d147773 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22078, d147773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22078, d147773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37286 (p : Pattern) (ha : d147737 p = 1) (hb : d170180 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22024 q = 1) (hb : d147719 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22024, d147719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22024, d147719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28209 q ha hb
  have h2 (q : Pattern) (ha : d21835 q = 1) (hb : d147601 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21835, d147601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28209 q ha hb
    | true =>
      simp only [d21835, d147601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22025 q = 1) (hb : d147720 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22025, d147720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22025, d147720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21836 q = 1) (hb : d147602 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21836, d147602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21836, d147602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22026 q = 1) (hb : d147721 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22026, d147721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22026, d147721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22027 q = 1) (hb : d147722 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22027, d147722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22027, d147722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d147726 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147727 q = 1) (hb : d170178 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147727, d170178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147727, d170178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d22033 q = 1) (hb : d147728 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22033, d147728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22033, d147728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37263 q ha hb
  have h10 (q : Pattern) (ha : d21841 q = 1) (hb : d147607 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21841, d147607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37263 q ha hb
    | true =>
      simp only [d21841, d147607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22034 q = 1) (hb : d147729 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22034, d147729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22034, d147729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21842 q = 1) (hb : d147608 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21842, d147608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21842, d147608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22035 q = 1) (hb : d147730 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22035, d147730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22035, d147730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22036 q = 1) (hb : d147731 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22036, d147731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22036, d147731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d147735 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d147736 q = 1) (hb : d170179 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147736, d170179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d147736, d170179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d147737 q = 1) (hb : d170180 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147737, d170180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147737, d170180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro37287 (p : Pattern) (ha : d147744 p = 1) (hb : d170183 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22028 q = 1) (hb : d147723 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22028, d147723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22028, d147723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28192 q ha hb
  have h2 (q : Pattern) (ha : d21737 q = 1) (hb : d147503 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21737, d147503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28192 q ha hb
    | true =>
      simp only [d21737, d147503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22029 q = 1) (hb : d147724 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22029, d147724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22029, d147724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21738 q = 1) (hb : d147504 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21738, d147504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21738, d147504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22030 q = 1) (hb : d147725 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22030, d147725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22030, d147725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22031 q = 1) (hb : d147726 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22031, d147726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22031, d147726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d147741 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147742 q = 1) (hb : d170181 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147742, d170181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147742, d170181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d22037 q = 1) (hb : d147732 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22037, d147732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22037, d147732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37248 q ha hb
  have h10 (q : Pattern) (ha : d21748 q = 1) (hb : d147514 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21748, d147514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37248 q ha hb
    | true =>
      simp only [d21748, d147514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22038 q = 1) (hb : d147733 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22038, d147733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22038, d147733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d21749 q = 1) (hb : d147515 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21749, d147515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d21749, d147515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22039 q = 1) (hb : d147734 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22039, d147734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22039, d147734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22040 q = 1) (hb : d147735 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22040, d147735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22040, d147735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d147743 q = 1) (hb : d170182 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147743, d170182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d147743, d170182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d147744 q = 1) (hb : d170183 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147744, d170183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147744, d170183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro37288 (p : Pattern) (ha : d147754 p = 1) (hb : d170188 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22053 q = 1) (hb : d147748 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22053, d147748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22053, d147748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29766 q ha hb
  have h2 (q : Pattern) (ha : d21851 q = 1) (hb : d147617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21851, d147617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29766 q ha hb
    | true =>
      simp only [d21851, d147617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22054 q = 1) (hb : d147749 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22054, d147749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22054, d147749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21852 q = 1) (hb : d147618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21852, d147618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21852, d147618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22055 q = 1) (hb : d147750 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22055, d147750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22055, d147750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22056 q = 1) (hb : d147751 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22056, d147751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22056, d147751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147752 q = 1) (hb : d170187 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147752, d170187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147752, d170187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d13164 q = 1) (hb : d113456 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
  have h10 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13165 q = 1) (hb : d113457 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13166 q = 1) (hb : d113458 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13167 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22058 q = 1) (hb : d147753 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22058, d147753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22058, d147753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d147754 q = 1) (hb : d170188 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147754, d170188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147754, d170188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37289 (p : Pattern) (ha : d147764 p = 1) (hb : d170194 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22043 q = 1) (hb : d147738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22043, d147738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22043, d147738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28193 q ha hb
  have h2 (q : Pattern) (ha : d21742 q = 1) (hb : d147508 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21742, d147508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28193 q ha hb
    | true =>
      simp only [d21742, d147508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22044 q = 1) (hb : d147739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22044, d147739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22044, d147739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21743 q = 1) (hb : d147509 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21743, d147509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21743, d147509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22045 q = 1) (hb : d147740 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22045, d147740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22045, d147740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22046 q = 1) (hb : d147741 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22046, d147741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22046, d147741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d147762 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d147763 q = 1) (hb : d170193 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147763, d170193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147763, d170193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d13164 q = 1) (hb : d113456 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13164, d113456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
  have h10 (q : Pattern) (ha : d13025 q = 1) (hb : d113355 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29765 q ha hb
    | true =>
      simp only [d13025, d113355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13165 q = 1) (hb : d113457 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13165, d113457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13026 q = 1) (hb : d113356 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13026, d113356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13166 q = 1) (hb : d113458 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13166, d113458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13167 q = 1) (hb : d113459 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13167, d113459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22058 q = 1) (hb : d147753 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22058, d147753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22058, d147753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d147764 q = 1) (hb : d170194 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147764, d170194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147764, d170194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37290 (p : Pattern) (ha : d147779 p = 1) (hb : d170203 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147745 q = 1) (hb : d170184 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147745, d170184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37286 q ha hb
    | true =>
      simp only [d147745, d170184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37287 q ha hb
  have h2 (q : Pattern) (ha : d147746 q = 1) (hb : d170185 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147746, d170185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147746, d170185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147747 q = 1) (hb : d170186 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147747, d170186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147747, d170186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147755 q = 1) (hb : d170189 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147755, d170189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37287 q ha hb
    | true =>
      simp only [d147755, d170189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37288 q ha hb
  have h5 (q : Pattern) (ha : d147756 q = 1) (hb : d170190 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147756, d170190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147756, d170190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147757 q = 1) (hb : d170191 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147757, d170191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147757, d170191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147758 q = 1) (hb : d170192 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147758, d170192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147758, d170192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147765 q = 1) (hb : d170195 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37287 q ha hb
    | true =>
      simp only [d147765, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
  have h9 (q : Pattern) (ha : d147766 q = 1) (hb : d170196 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147767 q = 1) (hb : d170197 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147774 q = 1) (hb : d170198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
    | true =>
      simp only [d147774, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37285 q hb ha
  have h12 (q : Pattern) (ha : d147775 q = 1) (hb : d170199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147776 q = 1) (hb : d170200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147777 q = 1) (hb : d170201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147777, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147778 q = 1) (hb : d170202 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147778, d170202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147778, d170202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147779 q = 1) (hb : d170203 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147779, d170203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147779, d170203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro37291 (p : Pattern) (ha : d147784 p = 1) (hb : d170208 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147765 q = 1) (hb : d170195 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37287 q ha hb
    | true =>
      simp only [d147765, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
  have h2 (q : Pattern) (ha : d147766 q = 1) (hb : d170196 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147767 q = 1) (hb : d170197 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147774 q = 1) (hb : d170198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
    | true =>
      simp only [d147774, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37285 q hb ha
  have h5 (q : Pattern) (ha : d147775 q = 1) (hb : d170199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147776 q = 1) (hb : d170200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147777 q = 1) (hb : d170201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147777, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147782 q = 1) (hb : d170206 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147782, d170206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147782, d170206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147783 q = 1) (hb : d170207 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147783, d170207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147783, d170207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147784 q = 1) (hb : d170208 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147784, d170208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147784, d170208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37292 (p : Pattern) (ha : d147790 p = 1) (hb : d170214 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147780 q = 1) (hb : d170204 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147780, d170204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37290 q ha hb
    | true =>
      simp only [d147780, d170204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147781 q = 1) (hb : d170205 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147781, d170205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147781, d170205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147785 q = 1) (hb : d170209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147785, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37291 q ha hb
    | true =>
      simp only [d147785, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147786 q = 1) (hb : d170210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147786, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147786, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147787 q = 1) (hb : d170211 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147787, d170211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147787, d170211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147788 q = 1) (hb : d170212 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147788, d170212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147788, d170212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147789 q = 1) (hb : d170213 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147789, d170213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147789, d170213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147790 q = 1) (hb : d170214 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147790, d170214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147790, d170214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37293 (p : Pattern) (ha : d22097 p = 1) (hb : d147792 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22064 q = 1) (hb : d147759 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22064, d147759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22064, d147759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
  have h2 (q : Pattern) (ha : d21755 q = 1) (hb : d147521 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28195 q ha hb
    | true =>
      simp only [d21755, d147521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22065 q = 1) (hb : d147760 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22065, d147760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22065, d147760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d21756 q = 1) (hb : d147522 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d21756, d147522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22066 q = 1) (hb : d147761 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22066, d147761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22066, d147761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22067 q = 1) (hb : d147762 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22067, d147762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22067, d147762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22096 q = 1) (hb : d147791 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22096, d147791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22096, d147791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15019 q = 1) (hb : d123144 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15019, d123144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
  have h9 (q : Pattern) (ha : d9844 q = 1) (hb : d101365 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23305 q ha hb
    | true =>
      simp only [d9844, d101365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15020 q = 1) (hb : d123145 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15020, d123145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9846 q = 1) (hb : d101367 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d9846, d101367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15021 q = 1) (hb : d123146 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15021, d123146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15022 q = 1) (hb : d123147 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15022, d123147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15023 q = 1) (hb : d123148 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15023, d123148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22097 q = 1) (hb : d147792 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22097, d147792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22097, d147792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37294 (p : Pattern) (ha : d147798 p = 1) (hb : d170220 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147793 q = 1) (hb : d170215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147793, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
    | true =>
      simp only [d147793, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37293 q hb ha
  have h2 (q : Pattern) (ha : d147794 q = 1) (hb : d170216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147794, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147794, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147795 q = 1) (hb : d170217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147795, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147795, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147796 q = 1) (hb : d170218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147796, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147796, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147797 q = 1) (hb : d170219 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147797, d170219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147797, d170219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147798 q = 1) (hb : d170220 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147798, d170220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147798, d170220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37295 (p : Pattern) (ha : d147804 p = 1) (hb : d170226 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147785 q = 1) (hb : d170209 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147785, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37291 q ha hb
    | true =>
      simp only [d147785, d170209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147786 q = 1) (hb : d170210 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147786, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147786, d170210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147799 q = 1) (hb : d170221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37294 q ha hb
    | true =>
      simp only [d147799, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147800 q = 1) (hb : d170222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147801 q = 1) (hb : d170223 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147801, d170223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147801, d170223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147802 q = 1) (hb : d170224 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147802, d170224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147802, d170224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147803 q = 1) (hb : d170225 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147803, d170225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147803, d170225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147804 q = 1) (hb : d170226 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147804, d170226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147804, d170226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37296 (p : Pattern) (ha : d147826 p = 1) (hb : d170234 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147765 q = 1) (hb : d170195 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37287 q ha hb
    | true =>
      simp only [d147765, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
  have h2 (q : Pattern) (ha : d147766 q = 1) (hb : d170196 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147767 q = 1) (hb : d170197 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147774 q = 1) (hb : d170198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
    | true =>
      simp only [d147774, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37285 q hb ha
  have h5 (q : Pattern) (ha : d147775 q = 1) (hb : d170199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147776 q = 1) (hb : d170200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147777 q = 1) (hb : d170201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147777, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147821 q = 1) (hb : d170229 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147821, d170229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
    | true =>
      simp only [d147821, d170229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29796 q hb ha
  have h9 (q : Pattern) (ha : d147822 q = 1) (hb : d170230 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147822, d170230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147822, d170230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147823 q = 1) (hb : d170231 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147823, d170231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147823, d170231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147824 q = 1) (hb : d170232 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147824, d170232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147824, d170232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147825 q = 1) (hb : d170233 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147825, d170233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147825, d170233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147826 q = 1) (hb : d170234 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147826, d170234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147826, d170234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37297 (p : Pattern) (ha : d147832 p = 1) (hb : d170240 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147827 q = 1) (hb : d170235 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147827, d170235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37296 q ha hb
    | true =>
      simp only [d147827, d170235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147828 q = 1) (hb : d170236 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147828, d170236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147828, d170236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147829 q = 1) (hb : d170237 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147829, d170237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147829, d170237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147830 q = 1) (hb : d170238 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147830, d170238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147830, d170238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147831 q = 1) (hb : d170239 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147831, d170239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147831, d170239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147832 q = 1) (hb : d170240 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147832, d170240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147832, d170240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37298 (p : Pattern) (ha : d147838 p = 1) (hb : d170246 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147805 q = 1) (hb : d170227 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147805, d170227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37292 q ha hb
    | true =>
      simp only [d147805, d170227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37295 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147818 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147819 q = 1) (hb : d170228 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147819, d170228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147819, d170228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d147833 q = 1) (hb : d170241 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147833, d170241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37297 q ha hb
    | true =>
      simp only [d147833, d170241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147834 q = 1) (hb : d170242 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147834, d170242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147834, d170242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147835 q = 1) (hb : d170243 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147835, d170243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147835, d170243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147836 q = 1) (hb : d170244 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147836, d170244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147836, d170244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147837 q = 1) (hb : d170245 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147837, d170245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147837, d170245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147838 q = 1) (hb : d170246 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147838, d170246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147838, d170246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37299 (p : Pattern) (ha : d147817 p = 1) (hb : d170251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147799 q = 1) (hb : d170221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37294 q ha hb
    | true =>
      simp only [d147799, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147800 q = 1) (hb : d170222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147814 q = 1) (hb : d170248 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147814, d170248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147814, d170248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147815 q = 1) (hb : d170249 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147815, d170249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147815, d170249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147816 q = 1) (hb : d170250 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147816, d170250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147816, d170250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147817 q = 1) (hb : d170251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147817, d170251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147817, d170251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37300 (p : Pattern) (ha : d147845 p = 1) (hb : d170257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147840 q = 1) (hb : d170252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147840, d170252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37299 q ha hb
    | true =>
      simp only [d147840, d170252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147841 q = 1) (hb : d170253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147841, d170253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147841, d170253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147842 q = 1) (hb : d170254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147842, d170254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147842, d170254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147843 q = 1) (hb : d170255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147843, d170255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147843, d170255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147844 q = 1) (hb : d170256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147844, d170256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147844, d170256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147845 q = 1) (hb : d170257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147845, d170257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147845, d170257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37301 (p : Pattern) (ha : d147851 p = 1) (hb : d170263 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147570 q = 1) (hb : d170045 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147570, d170045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147570, d170045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37255 q ha hb
  have h2 (q : Pattern) (ha : d147571 q = 1) (hb : d170046 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147571, d170046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147571, d170046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147580 q = 1) (hb : d170055 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147580, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37255 q ha hb
    | true =>
      simp only [d147580, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37258 q ha hb
  have h4 (q : Pattern) (ha : d147581 q = 1) (hb : d170056 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147581, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147581, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147582 q = 1) (hb : d170057 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147582, d170057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147582, d170057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147687 q = 1) (hb : d170146 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147687, d170146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37272 q ha hb
    | true =>
      simp only [d147687, d170146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37280 q ha hb
  have h7 (q : Pattern) (ha : d147705 q = 1) (hb : d170164 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147705, d170164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37281 q ha hb
    | true =>
      simp only [d147705, d170164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37282 q ha hb
  have h8 (q : Pattern) (ha : d147706 q = 1) (hb : d170165 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147706, d170165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147706, d170165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147707 q = 1) (hb : d170166 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147707, d170166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147707, d170166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d147708 q = 1) (hb : d170167 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147708, d170167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147708, d170167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147712 q = 1) (hb : d170171 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147712, d170171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147712, d170171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37283 q ha hb
  have h12 (q : Pattern) (ha : d147714 q = 1) (hb : d170173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147714, d170173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147714, d170173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37284 q ha hb
  have h13 (q : Pattern) (ha : d147715 q = 1) (hb : d170174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147715, d170174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d147715, d170174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147716 q = 1) (hb : d170175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147716, d170175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147716, d170175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d147717 q = 1) (hb : d170176 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147717, d170176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d147717, d170176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d147718 q = 1) (hb : d170177 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147718, d170177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147718, d170177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147839 q = 1) (hb : d170247 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147839, d170247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147839, d170247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37298 q ha hb
  have h18 (q : Pattern) (ha : d147846 q = 1) (hb : d170258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147846, d170258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147846, d170258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37300 q ha hb
  have h19 (q : Pattern) (ha : d147847 q = 1) (hb : d170259 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147847, d170259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147847, d170259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d147848 q = 1) (hb : d170260 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147848, d170260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d147848, d170260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d147849 q = 1) (hb : d170261 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147849, d170261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d147849, d170261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d147850 q = 1) (hb : d170262 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147850, d170262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d147850, d170262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d147851 q = 1) (hb : d170263 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147851, d170263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147851, d170263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro37302 (p : Pattern) (ha : d147857 p = 1) (hb : d170269 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147852 q = 1) (hb : d170264 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147852, d170264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147852, d170264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37301 q ha hb
  have h2 (q : Pattern) (ha : d147853 q = 1) (hb : d170265 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147853, d170265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147853, d170265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147854 q = 1) (hb : d170266 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147854, d170266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147854, d170266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147855 q = 1) (hb : d170267 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147855, d170267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147855, d170267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147856 q = 1) (hb : d170268 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147856, d170268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147856, d170268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147857 q = 1) (hb : d170269 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147857, d170269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147857, d170269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37303 (p : Pattern) (ha : d22249 p = 1) (hb : d147891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22244 q = 1) (hb : d147886 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22244, d147886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29805 q ha hb
    | true =>
      simp only [d22244, d147886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22245 q = 1) (hb : d147887 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22245, d147887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22245, d147887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22246 q = 1) (hb : d147888 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22246, d147888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22246, d147888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22247 q = 1) (hb : d147889 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22247, d147889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22247, d147889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22248 q = 1) (hb : d147890 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22248, d147890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22248, d147890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d123248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22249 q = 1) (hb : d147891 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22249, d147891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22249, d147891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37304 (p : Pattern) (ha : d22255 p = 1) (hb : d147897 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22233 q = 1) (hb : d147875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
    | true =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22234 q = 1) (hb : d147876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22235 q = 1) (hb : d147877 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22235, d147877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22235, d147877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22236 q = 1) (hb : d147878 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22236, d147878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22236, d147878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22254 q = 1) (hb : d147896 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22254, d147896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22254, d147896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15163 q = 1) (hb : d123248 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15163, d123248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15164 q = 1) (hb : d123249 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15164, d123249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15165 q = 1) (hb : d123250 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15165, d123250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22255 q = 1) (hb : d147897 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22255, d147897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22255, d147897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37305 (p : Pattern) (ha : d22225 p = 1) (hb : d147867 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h3 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10051 q = 1) (hb : d101478 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10051, d101478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h5 (q : Pattern) (ha : d10052 q = 1) (hb : d101479 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10052, d101479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h6 (q : Pattern) (ha : d10053 q = 1) (hb : d101480 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d10053, d101480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d22225 q = 1) (hb : d147867 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d22225, d147867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22225, d147867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h7 p ha hb
theorem andIntro37306 (p : Pattern) (ha : d147873 p = 1) (hb : d170275 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10038 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d16859 q = 1) (hb : d127633 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d16859, d127633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d16860 q = 1) (hb : d127634 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d16860, d127634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d16860, d127634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147865 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147866 q = 1) (hb : d170273 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147866, d170273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147866, d170273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d22226 q = 1) (hb : d147868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d147868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37305 q ha hb
    | true =>
      simp only [d22226, d147868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d22227 q = 1) (hb : d147869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d147869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22227, d147869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d22228 q = 1) (hb : d147870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22228, d147870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22228, d147870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d22229 q = 1) (hb : d147871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22229, d147871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22229, d147871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147872 q = 1) (hb : d170274 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147872, d170274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147872, d170274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d147873 q = 1) (hb : d170275 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147873, d170275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147873, d170275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  exact h13 p ha hb
theorem andIntro37307 (p : Pattern) (ha : d147881 p = 1) (hb : d170277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22220 q = 1) (hb : d147862 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d147862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28245 q ha hb
    | true =>
      simp only [d22220, d147862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22221 q = 1) (hb : d147863 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d147863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22221, d147863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22222 q = 1) (hb : d147864 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22222, d147864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22222, d147864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22223 q = 1) (hb : d147865 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22223, d147865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22223, d147865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147878 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147879 q = 1) (hb : d170276 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147879, d170276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147879, d170276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13353 q = 1) (hb : d113613 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13354 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22238 q = 1) (hb : d147880 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22238, d147880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22238, d147880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d147881 q = 1) (hb : d170277 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147881, d170277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147881, d170277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37308 (p : Pattern) (ha : d147903 p = 1) (hb : d170290 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147882 q = 1) (hb : d170278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37306 q ha hb
    | true =>
      simp only [d147882, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
  have h2 (q : Pattern) (ha : d147883 q = 1) (hb : d170279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147884 q = 1) (hb : d170280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147892 q = 1) (hb : d170281 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
    | true =>
      simp only [d147892, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37303 q hb ha
  have h5 (q : Pattern) (ha : d147893 q = 1) (hb : d170282 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147894 q = 1) (hb : d170283 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147895 q = 1) (hb : d170284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147895, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147898 q = 1) (hb : d170285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147898, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
    | true =>
      simp only [d147898, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37304 q hb ha
  have h9 (q : Pattern) (ha : d147899 q = 1) (hb : d170286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147899, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147899, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147900 q = 1) (hb : d170287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147900, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147900, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147901 q = 1) (hb : d170288 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147901, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147901, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147902 q = 1) (hb : d170289 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147902, d170289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147902, d170289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147903 q = 1) (hb : d170290 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147903, d170290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147903, d170290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37309 (p : Pattern) (ha : d147907 p = 1) (hb : d170294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147898 q = 1) (hb : d170285 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147898, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
    | true =>
      simp only [d147898, d170285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37304 q hb ha
  have h2 (q : Pattern) (ha : d147899 q = 1) (hb : d170286 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147899, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147899, d170286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147900 q = 1) (hb : d170287 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147900, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147900, d170287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147901 q = 1) (hb : d170288 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147901, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147901, d170288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147906 q = 1) (hb : d170293 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147906, d170293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147906, d170293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147907 q = 1) (hb : d170294 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147907, d170294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147907, d170294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37310 (p : Pattern) (ha : d147913 p = 1) (hb : d170300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37308 q ha hb
    | true =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d170298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147912 q = 1) (hb : d170299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147912, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147912, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147913 q = 1) (hb : d170300 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147913, d170300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147913, d170300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37311 (p : Pattern) (ha : d147917 p = 1) (hb : d170304 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d170302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147916 q = 1) (hb : d170303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147916, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147916, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147917 q = 1) (hb : d170304 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147917, d170304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147917, d170304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37312 (p : Pattern) (ha : d147923 p = 1) (hb : d170310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147918 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37310 q ha hb
    | true =>
      simp only [d147918, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37311 q ha hb
  have h2 (q : Pattern) (ha : d147919 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147919, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147919, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147920 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147920, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147920, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147921 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147921, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147921, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147922 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147922, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147922, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147923 q = 1) (hb : d170310 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147923, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147923, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37313 (p : Pattern) (ha : d147926 p = 1) (hb : d170313 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37308 q ha hb
    | true =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d170298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147912 q = 1) (hb : d170299 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147912, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147912, d170299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147926 q = 1) (hb : d170313 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147926, d170313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147926, d170313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37314 (p : Pattern) (ha : d147927 p = 1) (hb : d170314 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d170302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147916 q = 1) (hb : d170303 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147916, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147916, d170303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147927 q = 1) (hb : d170314 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147927, d170314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147927, d170314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37315 (p : Pattern) (ha : d147933 p = 1) (hb : d170320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147918 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37310 q ha hb
    | true =>
      simp only [d147918, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37311 q ha hb
  have h2 (q : Pattern) (ha : d147919 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147919, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147919, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147920 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147920, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147920, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147921 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147921, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147921, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147922 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147922, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147922, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147928 q = 1) (hb : d170315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37313 q ha hb
    | true =>
      simp only [d147928, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37314 q ha hb
  have h7 (q : Pattern) (ha : d147929 q = 1) (hb : d170316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147929, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147929, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147930 q = 1) (hb : d170317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147930, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147930, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147931 q = 1) (hb : d170318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147931, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147931, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147932 q = 1) (hb : d170319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147932, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147932, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147933 q = 1) (hb : d170320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147933, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147933, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37316 (p : Pattern) (ha : d147938 p = 1) (hb : d170325 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37308 q ha hb
    | true =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d170298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147937 q = 1) (hb : d170324 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147937, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147937, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147938 q = 1) (hb : d170325 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147938, d170325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147938, d170325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37317 (p : Pattern) (ha : d147940 p = 1) (hb : d170327 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d170302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147939 q = 1) (hb : d170326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147939, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147939, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147940 q = 1) (hb : d170327 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147940, d170327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147940, d170327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37318 (p : Pattern) (ha : d147947 p = 1) (hb : d170334 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37308 q ha hb
    | true =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147945 q = 1) (hb : d170332 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147945, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147945, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147946 q = 1) (hb : d170333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147946, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147946, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147947 q = 1) (hb : d170334 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147947, d170334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147947, d170334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37319 (p : Pattern) (ha : d147950 p = 1) (hb : d170337 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147948 q = 1) (hb : d170335 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147948, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147948, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147949 q = 1) (hb : d170336 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147949, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147949, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d147950 q = 1) (hb : d170337 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147950, d170337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147950, d170337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37320 (p : Pattern) (ha : d147961 p = 1) (hb : d170342 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22313 q = 1) (hb : d147955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, d147955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28261 q ha hb
    | true =>
      simp only [d22313, d147955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22314 q = 1) (hb : d147956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, d147956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22314, d147956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22315 q = 1) (hb : d147957 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22315, d147957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22315, d147957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22316 q = 1) (hb : d147958 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22316, d147958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22316, d147958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127634 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147959 q = 1) (hb : d170341 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147959, d170341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147959, d170341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d10046 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10048 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d15229 q = 1) (hb : d123314 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15229, d123314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15230 q = 1) (hb : d123315 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15230, d123315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15230, d123315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147871 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15231 q = 1) (hb : d147960 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15231, d147960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15231, d147960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147961 q = 1) (hb : d170342 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147961, d170342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147961, d170342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro37321 (p : Pattern) (ha : d147971 p = 1) (hb : d170347 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22324 q = 1) (hb : d147966 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d147966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29820 q ha hb
    | true =>
      simp only [d22324, d147966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22325 q = 1) (hb : d147967 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d147967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22325, d147967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22326 q = 1) (hb : d147968 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22326, d147968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22326, d147968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22327 q = 1) (hb : d147969 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22327, d147969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22327, d147969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147970 q = 1) (hb : d170346 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d147970, d170346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147970, d170346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13353 q = 1) (hb : d113613 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13353, d113613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13354 q = 1) (hb : d113614 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13354, d113614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22238 q = 1) (hb : d147880 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22238, d147880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22238, d147880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d147971 q = 1) (hb : d170347 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d147971, d170347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147971, d170347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37322 (p : Pattern) (ha : d147977 p = 1) (hb : d170353 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147962 q = 1) (hb : d170343 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147962, d170343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37320 q ha hb
    | true =>
      simp only [d147962, d170343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37306 q ha hb
  have h2 (q : Pattern) (ha : d147963 q = 1) (hb : d170344 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147963, d170344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147963, d170344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147964 q = 1) (hb : d170345 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147964, d170345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147964, d170345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147972 q = 1) (hb : d170348 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147972, d170348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37306 q ha hb
    | true =>
      simp only [d147972, d170348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37321 q ha hb
  have h5 (q : Pattern) (ha : d147973 q = 1) (hb : d170349 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147973, d170349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147973, d170349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147974 q = 1) (hb : d170350 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147974, d170350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147974, d170350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147975 q = 1) (hb : d170351 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147975, d170351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147975, d170351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147882 q = 1) (hb : d170278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37306 q ha hb
    | true =>
      simp only [d147882, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
  have h9 (q : Pattern) (ha : d147883 q = 1) (hb : d170279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147884 q = 1) (hb : d170280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147892 q = 1) (hb : d170281 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
    | true =>
      simp only [d147892, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37303 q hb ha
  have h12 (q : Pattern) (ha : d147893 q = 1) (hb : d170282 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147894 q = 1) (hb : d170283 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d147895 q = 1) (hb : d170284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147895, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d147976 q = 1) (hb : d170352 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147976, d170352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147976, d170352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d147977 q = 1) (hb : d170353 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147977, d170353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147977, d170353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro37323 (p : Pattern) (ha : d147982 p = 1) (hb : d170358 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147882 q = 1) (hb : d170278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37306 q ha hb
    | true =>
      simp only [d147882, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
  have h2 (q : Pattern) (ha : d147883 q = 1) (hb : d170279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147884 q = 1) (hb : d170280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147892 q = 1) (hb : d170281 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
    | true =>
      simp only [d147892, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37303 q hb ha
  have h5 (q : Pattern) (ha : d147893 q = 1) (hb : d170282 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147894 q = 1) (hb : d170283 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147895 q = 1) (hb : d170284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147895, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147980 q = 1) (hb : d170356 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147980, d170356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147980, d170356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d147981 q = 1) (hb : d170357 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147981, d170357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147981, d170357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147982 q = 1) (hb : d170358 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147982, d170358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147982, d170358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37324 (p : Pattern) (ha : d147988 p = 1) (hb : d170364 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147978 q = 1) (hb : d170354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147978, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37322 q ha hb
    | true =>
      simp only [d147978, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147979 q = 1) (hb : d170355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147979, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147979, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147983 q = 1) (hb : d170359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37323 q ha hb
    | true =>
      simp only [d147983, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147984 q = 1) (hb : d170360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147985 q = 1) (hb : d170361 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147985, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147985, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147986 q = 1) (hb : d170362 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147986, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147986, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147987 q = 1) (hb : d170363 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147987, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147987, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147988 q = 1) (hb : d170364 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147988, d170364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147988, d170364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37325 (p : Pattern) (ha : d147992 p = 1) (hb : d170368 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147983 q = 1) (hb : d170359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37323 q ha hb
    | true =>
      simp only [d147983, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147984 q = 1) (hb : d170360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147989 q = 1) (hb : d170365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147989, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147989, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147990 q = 1) (hb : d170366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147990, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147990, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147991 q = 1) (hb : d170367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147991, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147991, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147992 q = 1) (hb : d170368 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147992, d170368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147992, d170368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37326 (p : Pattern) (ha : d148001 p = 1) (hb : d170376 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147882 q = 1) (hb : d170278 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147882, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37306 q ha hb
    | true =>
      simp only [d147882, d170278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
  have h2 (q : Pattern) (ha : d147883 q = 1) (hb : d170279 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147883, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147883, d170279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147884 q = 1) (hb : d170280 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147884, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147884, d170280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147892 q = 1) (hb : d170281 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147892, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
    | true =>
      simp only [d147892, d170281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37303 q hb ha
  have h5 (q : Pattern) (ha : d147893 q = 1) (hb : d170282 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147893, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147893, d170282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147894 q = 1) (hb : d170283 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147894, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147894, d170283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147895 q = 1) (hb : d170284 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147895, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147895, d170284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147996 q = 1) (hb : d170371 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147996, d170371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37307 q ha hb
    | true =>
      simp only [d147996, d170371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29826 q hb ha
  have h9 (q : Pattern) (ha : d147997 q = 1) (hb : d170372 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147997, d170372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147997, d170372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147998 q = 1) (hb : d170373 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147998, d170373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147998, d170373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147999 q = 1) (hb : d170374 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147999, d170374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147999, d170374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148000 q = 1) (hb : d170375 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148000, d170375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148000, d170375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148001 q = 1) (hb : d170376 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148001, d170376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148001, d170376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37327 (p : Pattern) (ha : d148007 p = 1) (hb : d170382 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148002 q = 1) (hb : d170377 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148002, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37326 q ha hb
    | true =>
      simp only [d148002, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148003 q = 1) (hb : d170378 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148003, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148003, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148004 q = 1) (hb : d170379 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148004, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148004, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148005 q = 1) (hb : d170380 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148005, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148005, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148006 q = 1) (hb : d170381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148006, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148006, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148007 q = 1) (hb : d170382 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148007, d170382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148007, d170382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37328 (p : Pattern) (ha : d148013 p = 1) (hb : d170388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147941 q = 1) (hb : d170328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147941, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37316 q ha hb
    | true =>
      simp only [d147941, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37317 q ha hb
  have h2 (q : Pattern) (ha : d147942 q = 1) (hb : d170329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147942, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147942, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147943 q = 1) (hb : d170330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147943, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147943, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147944 q = 1) (hb : d170331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147944, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147944, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147951 q = 1) (hb : d170338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147951, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37318 q ha hb
    | true =>
      simp only [d147951, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37319 q ha hb
  have h6 (q : Pattern) (ha : d147952 q = 1) (hb : d170339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147952, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147952, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147953 q = 1) (hb : d170340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147953, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147953, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147993 q = 1) (hb : d170369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147993, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37324 q ha hb
    | true =>
      simp only [d147993, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37325 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147918 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147994 q = 1) (hb : d170370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147994, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148008 q = 1) (hb : d170383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148008, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37327 q ha hb
    | true =>
      simp only [d148008, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148009 q = 1) (hb : d170384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148009, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148009, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148010 q = 1) (hb : d170385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148010, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148011 q = 1) (hb : d170386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148011, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148012 q = 1) (hb : d170387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148012, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148013 q = 1) (hb : d170388 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148013, d170388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148013, d170388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37329 (p : Pattern) (ha : d148014 p = 1) (hb : d170389 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37308 q ha hb
    | true =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147911 q = 1) (hb : d170298 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147911, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147911, d170298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147937 q = 1) (hb : d170324 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147937, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147937, d170324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148014 q = 1) (hb : d170389 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148014, d170389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148014, d170389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37330 (p : Pattern) (ha : d148015 p = 1) (hb : d170390 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147915 q = 1) (hb : d170302 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147915, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147915, d170302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147939 q = 1) (hb : d170326 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147939, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147939, d170326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148015 q = 1) (hb : d170390 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148015, d170390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148015, d170390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37331 (p : Pattern) (ha : d148020 p = 1) (hb : d170395 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147904 q = 1) (hb : d170291 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37308 q ha hb
    | true =>
      simp only [d147904, d170291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147905 q = 1) (hb : d170292 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147905, d170292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147910 q = 1) (hb : d170297 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147910, d170297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147945 q = 1) (hb : d170332 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147945, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147945, d170332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147946 q = 1) (hb : d170333 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147946, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147946, d170333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148020 q = 1) (hb : d170395 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148020, d170395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148020, d170395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37332 (p : Pattern) (ha : d148021 p = 1) (hb : d170396 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147914 q = 1) (hb : d170301 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147914, d170301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147948 q = 1) (hb : d170335 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147948, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147948, d170335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147949 q = 1) (hb : d170336 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147949, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147949, d170336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148021 q = 1) (hb : d170396 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148021, d170396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148021, d170396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37333 (p : Pattern) (ha : d148025 p = 1) (hb : d170400 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147978 q = 1) (hb : d170354 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147978, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37322 q ha hb
    | true =>
      simp only [d147978, d170354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147979 q = 1) (hb : d170355 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147979, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147979, d170355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147983 q = 1) (hb : d170359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37323 q ha hb
    | true =>
      simp only [d147983, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147984 q = 1) (hb : d170360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147985 q = 1) (hb : d170361 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147985, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147985, d170361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147986 q = 1) (hb : d170362 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147986, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147986, d170362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147987 q = 1) (hb : d170363 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147987, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147987, d170363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148025 q = 1) (hb : d170400 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148025, d170400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148025, d170400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37334 (p : Pattern) (ha : d148026 p = 1) (hb : d170401 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147983 q = 1) (hb : d170359 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147983, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37323 q ha hb
    | true =>
      simp only [d147983, d170359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147984 q = 1) (hb : d170360 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147984, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147984, d170360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147908 q = 1) (hb : d170295 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37309 q ha hb
    | true =>
      simp only [d147908, d170295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147909 q = 1) (hb : d170296 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147909, d170296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147989 q = 1) (hb : d170365 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147989, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147989, d170365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147990 q = 1) (hb : d170366 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147990, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147990, d170366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147991 q = 1) (hb : d170367 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147991, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147991, d170367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148026 q = 1) (hb : d170401 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148026, d170401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148026, d170401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37335 (p : Pattern) (ha : d148029 p = 1) (hb : d170404 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148002 q = 1) (hb : d170377 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148002, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37326 q ha hb
    | true =>
      simp only [d148002, d170377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148003 q = 1) (hb : d170378 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148003, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148003, d170378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148004 q = 1) (hb : d170379 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148004, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148004, d170379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148005 q = 1) (hb : d170380 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148005, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148005, d170380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148006 q = 1) (hb : d170381 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148006, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148006, d170381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148029 q = 1) (hb : d170404 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148029, d170404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148029, d170404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37336 (p : Pattern) (ha : d148035 p = 1) (hb : d170410 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147941 q = 1) (hb : d170328 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147941, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37316 q ha hb
    | true =>
      simp only [d147941, d170328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37317 q ha hb
  have h2 (q : Pattern) (ha : d147942 q = 1) (hb : d170329 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147942, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147942, d170329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147943 q = 1) (hb : d170330 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147943, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147943, d170330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147944 q = 1) (hb : d170331 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147944, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147944, d170331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147951 q = 1) (hb : d170338 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147951, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37318 q ha hb
    | true =>
      simp only [d147951, d170338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37319 q ha hb
  have h6 (q : Pattern) (ha : d147952 q = 1) (hb : d170339 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147952, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147952, d170339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147953 q = 1) (hb : d170340 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147953, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147953, d170340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147993 q = 1) (hb : d170369 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147993, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37324 q ha hb
    | true =>
      simp only [d147993, d170369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37325 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147918 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d147994 q = 1) (hb : d170370 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147994, d170370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148008 q = 1) (hb : d170383 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148008, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37327 q ha hb
    | true =>
      simp only [d148008, d170383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148009 q = 1) (hb : d170384 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148009, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148009, d170384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148010 q = 1) (hb : d170385 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148010, d170385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148011 q = 1) (hb : d170386 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148011, d170386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148012 q = 1) (hb : d170387 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148012, d170387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148016 q = 1) (hb : d170391 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148016, d170391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37329 q ha hb
    | true =>
      simp only [d148016, d170391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37330 q ha hb
  have h17 (q : Pattern) (ha : d148017 q = 1) (hb : d170392 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148017, d170392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148017, d170392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148018 q = 1) (hb : d170393 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148018, d170393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148018, d170393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d148019 q = 1) (hb : d170394 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148019, d170394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148019, d170394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148022 q = 1) (hb : d170397 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148022, d170397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37331 q ha hb
    | true =>
      simp only [d148022, d170397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37332 q ha hb
  have h21 (q : Pattern) (ha : d148023 q = 1) (hb : d170398 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148023, d170398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148023, d170398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d148024 q = 1) (hb : d170399 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148024, d170399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148024, d170399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148027 q = 1) (hb : d170402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148027, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37333 q ha hb
    | true =>
      simp only [d148027, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37334 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d147928 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d148028 q = 1) (hb : d170403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d148028, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d148030 q = 1) (hb : d170405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148030, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37335 q ha hb
    | true =>
      simp only [d148030, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d148031 q = 1) (hb : d170406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148031, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d148031, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d148032 q = 1) (hb : d170407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d148032, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d148033 q = 1) (hb : d170408 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148033, d170408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d148033, d170408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d148034 q = 1) (hb : d170409 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148034, d170409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148034, d170409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d148035 q = 1) (hb : d170410 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148035, d170410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148035, d170410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro37337 (p : Pattern) (ha : d148047 p = 1) (hb : d170422 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148037 q = 1) (hb : d170412 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148037, d170412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37325 q ha hb
    | true =>
      simp only [d148037, d170412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37311 q ha hb
  have h2 (q : Pattern) (ha : d148038 q = 1) (hb : d170413 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148038, d170413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148038, d170413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148039 q = 1) (hb : d170414 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148039, d170414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148039, d170414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148040 q = 1) (hb : d170415 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148040, d170415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148040, d170415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148041 q = 1) (hb : d170416 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148041, d170416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148041, d170416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148042 q = 1) (hb : d170417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148042, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37311 q ha hb
    | true =>
      simp only [d148042, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148043 q = 1) (hb : d170418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148043, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148043, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148044 q = 1) (hb : d170419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148044, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148044, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148045 q = 1) (hb : d170420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148045, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148045, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148046 q = 1) (hb : d170421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148046, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148046, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148047 q = 1) (hb : d170422 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148047, d170422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148047, d170422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37338 (p : Pattern) (ha : d148053 p = 1) (hb : d170428 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148042 q = 1) (hb : d170417 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148042, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37311 q ha hb
    | true =>
      simp only [d148042, d170417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148043 q = 1) (hb : d170418 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148043, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148043, d170418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148044 q = 1) (hb : d170419 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148044, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148044, d170419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148045 q = 1) (hb : d170420 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148045, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148045, d170420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148046 q = 1) (hb : d170421 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148046, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148046, d170421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148048 q = 1) (hb : d170423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148048, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37314 q ha hb
    | true =>
      simp only [d148048, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148049 q = 1) (hb : d170424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148049, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148049, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148050 q = 1) (hb : d170425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148050, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148050, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148051 q = 1) (hb : d170426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148051, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148051, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148052 q = 1) (hb : d170427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148052, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148052, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148053 q = 1) (hb : d170428 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148053, d170428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148053, d170428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37339 (p : Pattern) (ha : d148060 p = 1) (hb : d170435 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148027 q = 1) (hb : d170402 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148027, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37333 q ha hb
    | true =>
      simp only [d148027, d170402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37334 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147928 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148028 q = 1) (hb : d170403 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148028, d170403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148030 q = 1) (hb : d170405 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148030, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37335 q ha hb
    | true =>
      simp only [d148030, d170405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148031 q = 1) (hb : d170406 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148031, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148031, d170406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148032 q = 1) (hb : d170407 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148032, d170407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148058 q = 1) (hb : d170433 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148058, d170433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148058, d170433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148059 q = 1) (hb : d170434 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148059, d170434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148059, d170434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148060 q = 1) (hb : d170435 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148060, d170435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148060, d170435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37340 (p : Pattern) (ha : d148062 p = 1) (hb : d170437 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148048 q = 1) (hb : d170423 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148048, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37314 q ha hb
    | true =>
      simp only [d148048, d170423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148049 q = 1) (hb : d170424 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148049, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148049, d170424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148050 q = 1) (hb : d170425 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148050, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148050, d170425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148051 q = 1) (hb : d170426 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148051, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148051, d170426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148052 q = 1) (hb : d170427 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148052, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148052, d170427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148062 q = 1) (hb : d170437 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148062, d170437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148062, d170437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37341 (p : Pattern) (ha : d22543 p = 1) (hb : d148114 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22538 q = 1) (hb : d148109 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22538, d148109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22538, d148109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29805 q ha hb
  have h2 (q : Pattern) (ha : d22244 q = 1) (hb : d147886 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22244, d147886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29805 q ha hb
    | true =>
      simp only [d22244, d147886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22539 q = 1) (hb : d148110 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22539, d148110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22539, d148110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22245 q = 1) (hb : d147887 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22245, d147887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22245, d147887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22540 q = 1) (hb : d148111 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22540, d148111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22540, d148111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22541 q = 1) (hb : d148112 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22541, d148112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22541, d148112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22542 q = 1) (hb : d148113 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22542, d148113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22542, d148113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22543 q = 1) (hb : d148114 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22543, d148114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22543, d148114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37342 (p : Pattern) (ha : d148078 p = 1) (hb : d170444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22497 q = 1) (hb : d148068 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22497, d148068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22497, d148068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28261 q ha hb
  have h2 (q : Pattern) (ha : d22313 q = 1) (hb : d147955 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22313, d147955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28261 q ha hb
    | true =>
      simp only [d22313, d147955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22498 q = 1) (hb : d148069 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22498, d148069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22498, d148069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22314 q = 1) (hb : d147956 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22314, d147956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22314, d147956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22499 q = 1) (hb : d148070 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22499, d148070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22499, d148070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22500 q = 1) (hb : d148071 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22500, d148071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22500, d148071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d127741 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d148072 q = 1) (hb : d170443 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148072, d170443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d148072, d170443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d15380 q = 1) (hb : d123419 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15380, d123419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
  have h10 (q : Pattern) (ha : d10046 q = 1) (hb : d101473 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23339 q ha hb
    | true =>
      simp only [d10046, d101473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d15381 q = 1) (hb : d123420 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15381, d123420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10048 q = 1) (hb : d101475 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10048, d101475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d15382 q = 1) (hb : d123421 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15382, d123421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d15382, d123421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d15383 q = 1) (hb : d123422 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15383, d123422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15383, d123422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d148076 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15384 q = 1) (hb : d148077 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15384, d148077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15384, d148077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148078 q = 1) (hb : d170444 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148078, d170444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148078, d170444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro37343 (p : Pattern) (ha : d148085 p = 1) (hb : d170447 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17004 q = 1) (hb : d127738 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17004, d127738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
  have h2 (q : Pattern) (ha : d10036 q = 1) (hb : d101463 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23338 q ha hb
    | true =>
      simp only [d10036, d101463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17005 q = 1) (hb : d127739 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17005, d127739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10038 q = 1) (hb : d101465 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10038, d101465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17006 q = 1) (hb : d127740 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17006, d127740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17007 q = 1) (hb : d127741 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17007, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17007, d127741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d148082 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d148083 q = 1) (hb : d170445 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148083, d170445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d148083, d170445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d22502 q = 1) (hb : d148073 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22502, d148073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22502, d148073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37305 q ha hb
  have h10 (q : Pattern) (ha : d22226 q = 1) (hb : d147868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22226, d147868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37305 q ha hb
    | true =>
      simp only [d22226, d147868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22503 q = 1) (hb : d148074 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22503, d148074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d22503, d148074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d22227 q = 1) (hb : d147869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22227, d147869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22227, d147869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d22504 q = 1) (hb : d148075 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22504, d148075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d22504, d148075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d22505 q = 1) (hb : d148076 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22505, d148076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d22505, d148076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d148084 q = 1) (hb : d170446 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148084, d170446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
    | true =>
      simp only [d148084, d170446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d148085 q = 1) (hb : d170447 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148085, d170447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148085, d170447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro37344 (p : Pattern) (ha : d148095 p = 1) (hb : d170452 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22518 q = 1) (hb : d148089 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22518, d148089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22518, d148089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29820 q ha hb
  have h2 (q : Pattern) (ha : d22324 q = 1) (hb : d147966 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22324, d147966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29820 q ha hb
    | true =>
      simp only [d22324, d147966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22519 q = 1) (hb : d148090 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22519, d148090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22519, d148090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22325 q = 1) (hb : d147967 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22325, d147967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22325, d147967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22520 q = 1) (hb : d148091 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22520, d148091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22520, d148091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22521 q = 1) (hb : d148092 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22521, d148092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22521, d148092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d148093 q = 1) (hb : d170451 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148093, d170451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d148093, d170451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d13490 q = 1) (hb : d113712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
  have h10 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13491 q = 1) (hb : d113713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13492 q = 1) (hb : d113714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13493 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22523 q = 1) (hb : d148094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22523, d148094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22523, d148094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d148095 q = 1) (hb : d170452 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148095, d170452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148095, d170452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37345 (p : Pattern) (ha : d148105 p = 1) (hb : d170458 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22508 q = 1) (hb : d148079 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22508, d148079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22508, d148079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28245 q ha hb
  have h2 (q : Pattern) (ha : d22220 q = 1) (hb : d147862 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22220, d147862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28245 q ha hb
    | true =>
      simp only [d22220, d147862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22509 q = 1) (hb : d148080 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22509, d148080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22509, d148080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22221 q = 1) (hb : d147863 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22221, d147863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22221, d147863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22510 q = 1) (hb : d148081 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22510, d148081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22510, d148081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22511 q = 1) (hb : d148082 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22511, d148082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22511, d148082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d148103 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d148104 q = 1) (hb : d170457 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148104, d170457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d148104, d170457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d13490 q = 1) (hb : d113712 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13490, d113712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
  have h10 (q : Pattern) (ha : d13351 q = 1) (hb : d113611 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29819 q ha hb
    | true =>
      simp only [d13351, d113611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13491 q = 1) (hb : d113713 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13491, d113713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13352 q = 1) (hb : d113612 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13352, d113612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13492 q = 1) (hb : d113714 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13492, d113714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13493 q = 1) (hb : d113715 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13493, d113715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22523 q = 1) (hb : d148094 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22523, d148094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22523, d148094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d148105 q = 1) (hb : d170458 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148105, d170458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148105, d170458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37346 (p : Pattern) (ha : d148120 p = 1) (hb : d170467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148086 q = 1) (hb : d170448 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148086, d170448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37342 q ha hb
    | true =>
      simp only [d148086, d170448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37343 q ha hb
  have h2 (q : Pattern) (ha : d148087 q = 1) (hb : d170449 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148087, d170449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148087, d170449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148088 q = 1) (hb : d170450 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148088, d170450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148088, d170450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148096 q = 1) (hb : d170453 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148096, d170453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37343 q ha hb
    | true =>
      simp only [d148096, d170453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37344 q ha hb
  have h5 (q : Pattern) (ha : d148097 q = 1) (hb : d170454 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148097, d170454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148097, d170454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148098 q = 1) (hb : d170455 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148098, d170455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148098, d170455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148099 q = 1) (hb : d170456 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148099, d170456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148099, d170456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148106 q = 1) (hb : d170459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37343 q ha hb
    | true =>
      simp only [d148106, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
  have h9 (q : Pattern) (ha : d148107 q = 1) (hb : d170460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148108 q = 1) (hb : d170461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148115 q = 1) (hb : d170462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
    | true =>
      simp only [d148115, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37341 q hb ha
  have h12 (q : Pattern) (ha : d148116 q = 1) (hb : d170463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148117 q = 1) (hb : d170464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148118 q = 1) (hb : d170465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148118, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148119 q = 1) (hb : d170466 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148119, d170466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148119, d170466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148120 q = 1) (hb : d170467 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148120, d170467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148120, d170467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro37347 (p : Pattern) (ha : d148125 p = 1) (hb : d170472 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148106 q = 1) (hb : d170459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37343 q ha hb
    | true =>
      simp only [d148106, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
  have h2 (q : Pattern) (ha : d148107 q = 1) (hb : d170460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148108 q = 1) (hb : d170461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148115 q = 1) (hb : d170462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
    | true =>
      simp only [d148115, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37341 q hb ha
  have h5 (q : Pattern) (ha : d148116 q = 1) (hb : d170463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148117 q = 1) (hb : d170464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148118 q = 1) (hb : d170465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148118, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148123 q = 1) (hb : d170470 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148123, d170470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148123, d170470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148124 q = 1) (hb : d170471 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148124, d170471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148124, d170471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148125 q = 1) (hb : d170472 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148125, d170472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148125, d170472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37348 (p : Pattern) (ha : d148131 p = 1) (hb : d170478 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148121 q = 1) (hb : d170468 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148121, d170468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37346 q ha hb
    | true =>
      simp only [d148121, d170468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148122 q = 1) (hb : d170469 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148122, d170469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148122, d170469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148126 q = 1) (hb : d170473 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148126, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37347 q ha hb
    | true =>
      simp only [d148126, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148127 q = 1) (hb : d170474 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148127, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148127, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148128 q = 1) (hb : d170475 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148128, d170475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148128, d170475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148129 q = 1) (hb : d170476 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148129, d170476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148129, d170476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148130 q = 1) (hb : d170477 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148130, d170477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148130, d170477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148131 q = 1) (hb : d170478 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148131, d170478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148131, d170478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37349 (p : Pattern) (ha : d22562 p = 1) (hb : d148133 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22529 q = 1) (hb : d148100 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22529, d148100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22529, d148100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
  have h2 (q : Pattern) (ha : d22233 q = 1) (hb : d147875 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28247 q ha hb
    | true =>
      simp only [d22233, d147875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22530 q = 1) (hb : d148101 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22530, d148101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22530, d148101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22234 q = 1) (hb : d147876 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22234, d147876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22531 q = 1) (hb : d148102 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22531, d148102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22531, d148102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22532 q = 1) (hb : d148103 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22532, d148103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22532, d148103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22561 q = 1) (hb : d148132 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22561, d148132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22561, d148132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15412 q = 1) (hb : d123451 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15412, d123451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
  have h9 (q : Pattern) (ha : d10135 q = 1) (hb : d101562 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23333 q ha hb
    | true =>
      simp only [d10135, d101562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15413 q = 1) (hb : d123452 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15413, d123452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10137 q = 1) (hb : d101564 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10137, d101564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15414 q = 1) (hb : d123453 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15414, d123453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15415 q = 1) (hb : d123454 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15415, d123454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15416 q = 1) (hb : d123455 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15416, d123455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22562 q = 1) (hb : d148133 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22562, d148133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22562, d148133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37350 (p : Pattern) (ha : d148139 p = 1) (hb : d170484 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148134 q = 1) (hb : d170479 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148134, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
    | true =>
      simp only [d148134, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37349 q hb ha
  have h2 (q : Pattern) (ha : d148135 q = 1) (hb : d170480 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148135, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148135, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148136 q = 1) (hb : d170481 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148136, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148136, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148137 q = 1) (hb : d170482 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148137, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148137, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148138 q = 1) (hb : d170483 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148138, d170483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148138, d170483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148139 q = 1) (hb : d170484 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148139, d170484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148139, d170484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37351 (p : Pattern) (ha : d148145 p = 1) (hb : d170490 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148126 q = 1) (hb : d170473 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148126, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37347 q ha hb
    | true =>
      simp only [d148126, d170473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148127 q = 1) (hb : d170474 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148127, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148127, d170474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148140 q = 1) (hb : d170485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37350 q ha hb
    | true =>
      simp only [d148140, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148141 q = 1) (hb : d170486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148142 q = 1) (hb : d170487 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148142, d170487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148142, d170487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148143 q = 1) (hb : d170488 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148143, d170488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148143, d170488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148144 q = 1) (hb : d170489 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148144, d170489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148144, d170489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148145 q = 1) (hb : d170490 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148145, d170490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148145, d170490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37352 (p : Pattern) (ha : d148167 p = 1) (hb : d170498 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148106 q = 1) (hb : d170459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37343 q ha hb
    | true =>
      simp only [d148106, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
  have h2 (q : Pattern) (ha : d148107 q = 1) (hb : d170460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148108 q = 1) (hb : d170461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148115 q = 1) (hb : d170462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
    | true =>
      simp only [d148115, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37341 q hb ha
  have h5 (q : Pattern) (ha : d148116 q = 1) (hb : d170463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148117 q = 1) (hb : d170464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148118 q = 1) (hb : d170465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148118, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148162 q = 1) (hb : d170493 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148162, d170493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
    | true =>
      simp only [d148162, d170493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29850 q hb ha
  have h9 (q : Pattern) (ha : d148163 q = 1) (hb : d170494 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148163, d170494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148163, d170494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148164 q = 1) (hb : d170495 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148164, d170495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148164, d170495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148165 q = 1) (hb : d170496 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148165, d170496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148165, d170496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148166 q = 1) (hb : d170497 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148166, d170497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148166, d170497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148167 q = 1) (hb : d170498 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148167, d170498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148167, d170498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37353 (p : Pattern) (ha : d148173 p = 1) (hb : d170504 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148168 q = 1) (hb : d170499 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148168, d170499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37352 q ha hb
    | true =>
      simp only [d148168, d170499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148169 q = 1) (hb : d170500 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148169, d170500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148169, d170500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148170 q = 1) (hb : d170501 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148170, d170501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148170, d170501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148171 q = 1) (hb : d170502 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148171, d170502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148171, d170502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148172 q = 1) (hb : d170503 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148172, d170503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148172, d170503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148173 q = 1) (hb : d170504 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148173, d170504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148173, d170504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37354 (p : Pattern) (ha : d148179 p = 1) (hb : d170510 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148146 q = 1) (hb : d170491 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148146, d170491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37348 q ha hb
    | true =>
      simp only [d148146, d170491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37351 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148159 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148160 q = 1) (hb : d170492 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148160, d170492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148160, d170492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148174 q = 1) (hb : d170505 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148174, d170505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37353 q ha hb
    | true =>
      simp only [d148174, d170505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148175 q = 1) (hb : d170506 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148175, d170506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148175, d170506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148176 q = 1) (hb : d170507 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148176, d170507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148176, d170507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148177 q = 1) (hb : d170508 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148177, d170508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148177, d170508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148178 q = 1) (hb : d170509 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148178, d170509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148178, d170509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148179 q = 1) (hb : d170510 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148179, d170510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148179, d170510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37355 (p : Pattern) (ha : d148158 p = 1) (hb : d170515 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148140 q = 1) (hb : d170485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37350 q ha hb
    | true =>
      simp only [d148140, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148141 q = 1) (hb : d170486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148155 q = 1) (hb : d170512 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148155, d170512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148155, d170512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148156 q = 1) (hb : d170513 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148156, d170513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148156, d170513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148157 q = 1) (hb : d170514 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148157, d170514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148157, d170514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148158 q = 1) (hb : d170515 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148158, d170515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148158, d170515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37356 (p : Pattern) (ha : d148186 p = 1) (hb : d170521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148181 q = 1) (hb : d170516 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148181, d170516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37355 q ha hb
    | true =>
      simp only [d148181, d170516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148182 q = 1) (hb : d170517 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148182, d170517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148182, d170517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148183 q = 1) (hb : d170518 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148183, d170518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148183, d170518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148184 q = 1) (hb : d170519 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148184, d170519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148184, d170519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148185 q = 1) (hb : d170520 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148185, d170520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148185, d170520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148186 q = 1) (hb : d170521 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148186, d170521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148186, d170521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37357 (p : Pattern) (ha : d148192 p = 1) (hb : d170527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147924 q = 1) (hb : d170311 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147924, d170311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147924, d170311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37312 q ha hb
  have h2 (q : Pattern) (ha : d147925 q = 1) (hb : d170312 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147925, d170312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147925, d170312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d147934 q = 1) (hb : d170321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147934, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37312 q ha hb
    | true =>
      simp only [d147934, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37315 q ha hb
  have h4 (q : Pattern) (ha : d147935 q = 1) (hb : d170322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147935, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147935, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d147936 q = 1) (hb : d170323 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147936, d170323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147936, d170323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148036 q = 1) (hb : d170411 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148036, d170411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37328 q ha hb
    | true =>
      simp only [d148036, d170411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37336 q ha hb
  have h7 (q : Pattern) (ha : d148054 q = 1) (hb : d170429 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148054, d170429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37337 q ha hb
    | true =>
      simp only [d148054, d170429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37338 q ha hb
  have h8 (q : Pattern) (ha : d148055 q = 1) (hb : d170430 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148055, d170430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148055, d170430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148056 q = 1) (hb : d170431 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148056, d170431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148056, d170431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d148057 q = 1) (hb : d170432 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148057, d170432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148057, d170432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148061 q = 1) (hb : d170436 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148061, d170436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148061, d170436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37339 q ha hb
  have h12 (q : Pattern) (ha : d148063 q = 1) (hb : d170438 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148063, d170438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148063, d170438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37340 q ha hb
  have h13 (q : Pattern) (ha : d148064 q = 1) (hb : d170439 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148064, d170439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148064, d170439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148065 q = 1) (hb : d170440 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148065, d170440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148065, d170440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148066 q = 1) (hb : d170441 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148066, d170441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d148066, d170441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d148067 q = 1) (hb : d170442 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148067, d170442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148067, d170442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148180 q = 1) (hb : d170511 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148180, d170511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148180, d170511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37354 q ha hb
  have h18 (q : Pattern) (ha : d148187 q = 1) (hb : d170522 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148187, d170522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148187, d170522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37356 q ha hb
  have h19 (q : Pattern) (ha : d148188 q = 1) (hb : d170523 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148188, d170523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148188, d170523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148189 q = 1) (hb : d170524 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148189, d170524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148189, d170524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d148190 q = 1) (hb : d170525 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148190, d170525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d148190, d170525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d148191 q = 1) (hb : d170526 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148191, d170526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148191, d170526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148192 q = 1) (hb : d170527 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148192, d170527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148192, d170527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro37358 (p : Pattern) (ha : d148198 p = 1) (hb : d170533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148193 q = 1) (hb : d170528 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148193, d170528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148193, d170528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37357 q ha hb
  have h2 (q : Pattern) (ha : d148194 q = 1) (hb : d170529 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148194, d170529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148194, d170529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148195 q = 1) (hb : d170530 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148195, d170530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148195, d170530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148196 q = 1) (hb : d170531 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148196, d170531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148196, d170531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148197 q = 1) (hb : d170532 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148197, d170532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148197, d170532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148198 q = 1) (hb : d170533 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148198, d170533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148198, d170533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37359 (p : Pattern) (ha : d22704 p = 1) (hb : d148222 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22699 q = 1) (hb : d148217 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22699, d148217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29859 q ha hb
    | true =>
      simp only [d22699, d148217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22700 q = 1) (hb : d148218 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22700, d148218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22700, d148218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22701 q = 1) (hb : d148219 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22701, d148219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22701, d148219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22702 q = 1) (hb : d148220 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22702, d148220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22702, d148220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22703 q = 1) (hb : d148221 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22703, d148221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22703, d148221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d123554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22704 q = 1) (hb : d148222 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22704, d148222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22704, d148222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37360 (p : Pattern) (ha : d22710 p = 1) (hb : d148228 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22688 q = 1) (hb : d148206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
    | true =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d22689 q = 1) (hb : d148207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22690 q = 1) (hb : d148208 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22690, d148208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22690, d148208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22691 q = 1) (hb : d148209 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22691, d148209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22691, d148209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22709 q = 1) (hb : d148227 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22709, d148227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d22709, d148227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15555 q = 1) (hb : d123554 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15555, d123554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d15556 q = 1) (hb : d123555 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15556, d123555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15557 q = 1) (hb : d123556 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d15557, d123556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22710 q = 1) (hb : d148228 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22710, d148228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22710, d148228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37361 (p : Pattern) (ha : d148204 p = 1) (hb : d170539 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17225 q = 1) (hb : d127927 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17225, d127927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17226 q = 1) (hb : d127928 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17226, d127928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d127856 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148203 q = 1) (hb : d170538 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148203, d170538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148203, d170538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d15545 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15545, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148204 q = 1) (hb : d170539 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148204, d170539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148204, d170539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro37362 (p : Pattern) (ha : d148212 p = 1) (hb : d170541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17153 q = 1) (hb : d127855 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17153, d127855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d17154 q = 1) (hb : d127856 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17154, d127856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148209 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148210 q = 1) (hb : d170540 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148210, d170540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148210, d170540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13680 q = 1) (hb : d113870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13681 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22693 q = 1) (hb : d148211 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d148211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22693, d148211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d148212 q = 1) (hb : d170541 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148212, d170541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148212, d170541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37363 (p : Pattern) (ha : d148234 p = 1) (hb : d170554 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148213 q = 1) (hb : d170542 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37361 q ha hb
    | true =>
      simp only [d148213, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
  have h2 (q : Pattern) (ha : d148214 q = 1) (hb : d170543 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148215 q = 1) (hb : d170544 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148223 q = 1) (hb : d170545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
    | true =>
      simp only [d148223, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37359 q hb ha
  have h5 (q : Pattern) (ha : d148224 q = 1) (hb : d170546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148225 q = 1) (hb : d170547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148226 q = 1) (hb : d170548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148226, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148229 q = 1) (hb : d170549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148229, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
    | true =>
      simp only [d148229, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37360 q hb ha
  have h9 (q : Pattern) (ha : d148230 q = 1) (hb : d170550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148230, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148230, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148231 q = 1) (hb : d170551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148231, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148231, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148232 q = 1) (hb : d170552 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148232, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148232, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148233 q = 1) (hb : d170553 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148233, d170553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148233, d170553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148234 q = 1) (hb : d170554 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148234, d170554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148234, d170554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37364 (p : Pattern) (ha : d148238 p = 1) (hb : d170558 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148229 q = 1) (hb : d170549 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148229, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
    | true =>
      simp only [d148229, d170549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37360 q hb ha
  have h2 (q : Pattern) (ha : d148230 q = 1) (hb : d170550 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148230, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148230, d170550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148231 q = 1) (hb : d170551 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148231, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148231, d170551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148232 q = 1) (hb : d170552 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148232, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148232, d170552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148237 q = 1) (hb : d170557 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148237, d170557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148237, d170557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148238 q = 1) (hb : d170558 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148238, d170558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148238, d170558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37365 (p : Pattern) (ha : d148244 p = 1) (hb : d170564 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37363 q ha hb
    | true =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d170562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148243 q = 1) (hb : d170563 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148243, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148243, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148244 q = 1) (hb : d170564 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148244, d170564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148244, d170564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37366 (p : Pattern) (ha : d148248 p = 1) (hb : d170568 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d170566 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148247 q = 1) (hb : d170567 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148247, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148247, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148248 q = 1) (hb : d170568 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148248, d170568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148248, d170568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37367 (p : Pattern) (ha : d148254 p = 1) (hb : d170574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148249 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37365 q ha hb
    | true =>
      simp only [d148249, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37366 q ha hb
  have h2 (q : Pattern) (ha : d148250 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148250, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148250, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148251 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148251, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148251, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148252 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148252, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148252, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148253 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148253, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148253, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148254 q = 1) (hb : d170574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148254, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148254, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37368 (p : Pattern) (ha : d148257 p = 1) (hb : d170577 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37363 q ha hb
    | true =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d170562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148243 q = 1) (hb : d170563 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148243, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148243, d170563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148257 q = 1) (hb : d170577 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148257, d170577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148257, d170577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37369 (p : Pattern) (ha : d148258 p = 1) (hb : d170578 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d170566 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148247 q = 1) (hb : d170567 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148247, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148247, d170567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148258 q = 1) (hb : d170578 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148258, d170578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148258, d170578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37370 (p : Pattern) (ha : d148264 p = 1) (hb : d170584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148249 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37365 q ha hb
    | true =>
      simp only [d148249, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37366 q ha hb
  have h2 (q : Pattern) (ha : d148250 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148250, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148250, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148251 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148251, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148251, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148252 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148252, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148252, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148253 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148253, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148253, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148259 q = 1) (hb : d170579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37368 q ha hb
    | true =>
      simp only [d148259, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37369 q ha hb
  have h7 (q : Pattern) (ha : d148260 q = 1) (hb : d170580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148260, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148260, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148261 q = 1) (hb : d170581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148261, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148261, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148262 q = 1) (hb : d170582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148262, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148262, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148263 q = 1) (hb : d170583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148263, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148263, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148264 q = 1) (hb : d170584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148264, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148264, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37371 (p : Pattern) (ha : d148269 p = 1) (hb : d170589 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37363 q ha hb
    | true =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d170562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148268 q = 1) (hb : d170588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148268, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148268, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148269 q = 1) (hb : d170589 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148269, d170589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148269, d170589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37372 (p : Pattern) (ha : d148271 p = 1) (hb : d170591 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d170566 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148270 q = 1) (hb : d170590 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148270, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148270, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148271 q = 1) (hb : d170591 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148271, d170591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148271, d170591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37373 (p : Pattern) (ha : d148278 p = 1) (hb : d170598 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37363 q ha hb
    | true =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148276 q = 1) (hb : d170596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148276, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148276, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148277 q = 1) (hb : d170597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148277, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148277, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148278 q = 1) (hb : d170598 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148278, d170598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148278, d170598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37374 (p : Pattern) (ha : d148281 p = 1) (hb : d170601 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148279 q = 1) (hb : d170599 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148279, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148279, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148280 q = 1) (hb : d170600 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148280, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148280, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148281 q = 1) (hb : d170601 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148281, d170601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148281, d170601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37375 (p : Pattern) (ha : d148290 p = 1) (hb : d170608 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13675 q = 1) (hb : d113865 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13675, d113865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d13676 q = 1) (hb : d113866 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13676, d113866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d15545 q = 1) (hb : d113872 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15545, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d15545, d113872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d13680 q = 1) (hb : d113870 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13680, d113870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d13681 q = 1) (hb : d113871 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13681, d113871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d22693 q = 1) (hb : d148211 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22693, d148211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d22693, d148211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d148290 q = 1) (hb : d170608 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148290, d170608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d148290, d170608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro37376 (p : Pattern) (ha : d148296 p = 1) (hb : d170614 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148286 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148287 q = 1) (hb : d170605 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148287, d170605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148287, d170605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37361 q ha hb
  have h3 (q : Pattern) (ha : d148288 q = 1) (hb : d170606 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148288, d170606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148288, d170606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148289 q = 1) (hb : d170607 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148289, d170607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148289, d170607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148291 q = 1) (hb : d170609 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148291, d170609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37361 q ha hb
    | true =>
      simp only [d148291, d170609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37375 q ha hb
  have h6 (q : Pattern) (ha : d148292 q = 1) (hb : d170610 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148292, d170610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148292, d170610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148293 q = 1) (hb : d170611 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148293, d170611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148293, d170611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148294 q = 1) (hb : d170612 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148294, d170612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148294, d170612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148213 q = 1) (hb : d170542 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37361 q ha hb
    | true =>
      simp only [d148213, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
  have h10 (q : Pattern) (ha : d148214 q = 1) (hb : d170543 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148215 q = 1) (hb : d170544 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d148223 q = 1) (hb : d170545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
    | true =>
      simp only [d148223, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37359 q hb ha
  have h13 (q : Pattern) (ha : d148224 q = 1) (hb : d170546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148225 q = 1) (hb : d170547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148226 q = 1) (hb : d170548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148226, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148295 q = 1) (hb : d170613 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148295, d170613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148295, d170613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148296 q = 1) (hb : d170614 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148296, d170614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148296, d170614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro37377 (p : Pattern) (ha : d148301 p = 1) (hb : d170619 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148213 q = 1) (hb : d170542 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37361 q ha hb
    | true =>
      simp only [d148213, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
  have h2 (q : Pattern) (ha : d148214 q = 1) (hb : d170543 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148215 q = 1) (hb : d170544 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148223 q = 1) (hb : d170545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
    | true =>
      simp only [d148223, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37359 q hb ha
  have h5 (q : Pattern) (ha : d148224 q = 1) (hb : d170546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148225 q = 1) (hb : d170547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148226 q = 1) (hb : d170548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148226, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148299 q = 1) (hb : d170617 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148299, d170617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148299, d170617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148300 q = 1) (hb : d170618 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148300, d170618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148300, d170618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148301 q = 1) (hb : d170619 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148301, d170619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148301, d170619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37378 (p : Pattern) (ha : d148307 p = 1) (hb : d170625 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148297 q = 1) (hb : d170615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148297, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37376 q ha hb
    | true =>
      simp only [d148297, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148298 q = 1) (hb : d170616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148298, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148298, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148302 q = 1) (hb : d170620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37377 q ha hb
    | true =>
      simp only [d148302, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148303 q = 1) (hb : d170621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148304 q = 1) (hb : d170622 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148304, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148304, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148305 q = 1) (hb : d170623 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148305, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148305, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148306 q = 1) (hb : d170624 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148306, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148306, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148307 q = 1) (hb : d170625 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148307, d170625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148307, d170625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37379 (p : Pattern) (ha : d148311 p = 1) (hb : d170629 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148302 q = 1) (hb : d170620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37377 q ha hb
    | true =>
      simp only [d148302, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148303 q = 1) (hb : d170621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148308 q = 1) (hb : d170626 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148308, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148308, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148309 q = 1) (hb : d170627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148309, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148309, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148310 q = 1) (hb : d170628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148310, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148310, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148311 q = 1) (hb : d170629 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148311, d170629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148311, d170629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37380 (p : Pattern) (ha : d148320 p = 1) (hb : d170637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148213 q = 1) (hb : d170542 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148213, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37361 q ha hb
    | true =>
      simp only [d148213, d170542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
  have h2 (q : Pattern) (ha : d148214 q = 1) (hb : d170543 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148214, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148214, d170543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148215 q = 1) (hb : d170544 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148215, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148215, d170544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148223 q = 1) (hb : d170545 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148223, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
    | true =>
      simp only [d148223, d170545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37359 q hb ha
  have h5 (q : Pattern) (ha : d148224 q = 1) (hb : d170546 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148224, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148224, d170546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148225 q = 1) (hb : d170547 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148225, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148225, d170547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148226 q = 1) (hb : d170548 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148226, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148226, d170548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148315 q = 1) (hb : d170632 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148315, d170632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37362 q ha hb
    | true =>
      simp only [d148315, d170632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29879 q hb ha
  have h9 (q : Pattern) (ha : d148316 q = 1) (hb : d170633 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148316, d170633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148316, d170633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148317 q = 1) (hb : d170634 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148317, d170634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148317, d170634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148318 q = 1) (hb : d170635 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148318, d170635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148318, d170635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148319 q = 1) (hb : d170636 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148319, d170636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148319, d170636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148320 q = 1) (hb : d170637 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148320, d170637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148320, d170637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37381 (p : Pattern) (ha : d148326 p = 1) (hb : d170643 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148321 q = 1) (hb : d170638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148321, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37380 q ha hb
    | true =>
      simp only [d148321, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148322 q = 1) (hb : d170639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148322, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148322, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148323 q = 1) (hb : d170640 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148323, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148323, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148324 q = 1) (hb : d170641 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148324, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148324, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148325 q = 1) (hb : d170642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148325, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148325, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148326 q = 1) (hb : d170643 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148326, d170643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148326, d170643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37382 (p : Pattern) (ha : d148332 p = 1) (hb : d170649 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148272 q = 1) (hb : d170592 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148272, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37371 q ha hb
    | true =>
      simp only [d148272, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37372 q ha hb
  have h2 (q : Pattern) (ha : d148273 q = 1) (hb : d170593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148273, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148273, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148274 q = 1) (hb : d170594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148274, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148274, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148275 q = 1) (hb : d170595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148275, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148275, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148282 q = 1) (hb : d170602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148282, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37373 q ha hb
    | true =>
      simp only [d148282, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37374 q ha hb
  have h6 (q : Pattern) (ha : d148283 q = 1) (hb : d170603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148283, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148283, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148284 q = 1) (hb : d170604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148284, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148284, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148312 q = 1) (hb : d170630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148312, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37378 q ha hb
    | true =>
      simp only [d148312, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37379 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148249 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148313 q = 1) (hb : d170631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148313, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148327 q = 1) (hb : d170644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148327, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37381 q ha hb
    | true =>
      simp only [d148327, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148328 q = 1) (hb : d170645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148328, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148328, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148329 q = 1) (hb : d170646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148329, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148330 q = 1) (hb : d170647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148330, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148331 q = 1) (hb : d170648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148331, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148332 q = 1) (hb : d170649 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148332, d170649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148332, d170649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro37383 (p : Pattern) (ha : d148333 p = 1) (hb : d170650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37363 q ha hb
    | true =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148242 q = 1) (hb : d170562 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148242, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148242, d170562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148268 q = 1) (hb : d170588 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148268, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148268, d170588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148333 q = 1) (hb : d170650 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148333, d170650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148333, d170650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37384 (p : Pattern) (ha : d148334 p = 1) (hb : d170651 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148246 q = 1) (hb : d170566 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148246, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148246, d170566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148270 q = 1) (hb : d170590 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148270, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148270, d170590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148334 q = 1) (hb : d170651 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148334, d170651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148334, d170651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37385 (p : Pattern) (ha : d148339 p = 1) (hb : d170656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148235 q = 1) (hb : d170555 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37363 q ha hb
    | true =>
      simp only [d148235, d170555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148236 q = 1) (hb : d170556 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148236, d170556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148241 q = 1) (hb : d170561 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148241, d170561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148276 q = 1) (hb : d170596 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148276, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148276, d170596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148277 q = 1) (hb : d170597 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148277, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148277, d170597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148339 q = 1) (hb : d170656 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148339, d170656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148339, d170656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37386 (p : Pattern) (ha : d148340 p = 1) (hb : d170657 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148245 q = 1) (hb : d170565 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148245, d170565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148279 q = 1) (hb : d170599 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148279, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148279, d170599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148280 q = 1) (hb : d170600 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148280, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148280, d170600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148340 q = 1) (hb : d170657 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148340, d170657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148340, d170657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37387 (p : Pattern) (ha : d148344 p = 1) (hb : d170661 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148297 q = 1) (hb : d170615 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148297, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37376 q ha hb
    | true =>
      simp only [d148297, d170615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148298 q = 1) (hb : d170616 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148298, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148298, d170616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148302 q = 1) (hb : d170620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37377 q ha hb
    | true =>
      simp only [d148302, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148303 q = 1) (hb : d170621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148304 q = 1) (hb : d170622 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148304, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148304, d170622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148305 q = 1) (hb : d170623 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148305, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148305, d170623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148306 q = 1) (hb : d170624 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148306, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148306, d170624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148344 q = 1) (hb : d170661 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148344, d170661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148344, d170661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37388 (p : Pattern) (ha : d148345 p = 1) (hb : d170662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148302 q = 1) (hb : d170620 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148302, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37377 q ha hb
    | true =>
      simp only [d148302, d170620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148303 q = 1) (hb : d170621 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148303, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148303, d170621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148239 q = 1) (hb : d170559 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37364 q ha hb
    | true =>
      simp only [d148239, d170559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148240 q = 1) (hb : d170560 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148240, d170560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148308 q = 1) (hb : d170626 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148308, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148308, d170626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148309 q = 1) (hb : d170627 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148309, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148309, d170627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148310 q = 1) (hb : d170628 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148310, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148310, d170628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148345 q = 1) (hb : d170662 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148345, d170662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148345, d170662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37389 (p : Pattern) (ha : d148348 p = 1) (hb : d170665 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148321 q = 1) (hb : d170638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148321, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37380 q ha hb
    | true =>
      simp only [d148321, d170638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148322 q = 1) (hb : d170639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148322, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148322, d170639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148323 q = 1) (hb : d170640 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148323, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148323, d170640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148324 q = 1) (hb : d170641 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148324, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148324, d170641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148325 q = 1) (hb : d170642 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148325, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148325, d170642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148348 q = 1) (hb : d170665 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148348, d170665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148348, d170665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37390 (p : Pattern) (ha : d148354 p = 1) (hb : d170671 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148272 q = 1) (hb : d170592 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148272, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37371 q ha hb
    | true =>
      simp only [d148272, d170592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37372 q ha hb
  have h2 (q : Pattern) (ha : d148273 q = 1) (hb : d170593 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148273, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148273, d170593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148274 q = 1) (hb : d170594 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148274, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148274, d170594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148275 q = 1) (hb : d170595 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148275, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148275, d170595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148282 q = 1) (hb : d170602 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148282, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37373 q ha hb
    | true =>
      simp only [d148282, d170602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37374 q ha hb
  have h6 (q : Pattern) (ha : d148283 q = 1) (hb : d170603 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148283, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148283, d170603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148284 q = 1) (hb : d170604 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148284, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148284, d170604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148312 q = 1) (hb : d170630 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148312, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37378 q ha hb
    | true =>
      simp only [d148312, d170630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37379 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148249 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d148313 q = 1) (hb : d170631 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148313, d170631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d148327 q = 1) (hb : d170644 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148327, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37381 q ha hb
    | true =>
      simp only [d148327, d170644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148328 q = 1) (hb : d170645 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148328, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148328, d170645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d148329 q = 1) (hb : d170646 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148329, d170646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148330 q = 1) (hb : d170647 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148330, d170647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148331 q = 1) (hb : d170648 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148331, d170648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148335 q = 1) (hb : d170652 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148335, d170652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37383 q ha hb
    | true =>
      simp only [d148335, d170652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37384 q ha hb
  have h17 (q : Pattern) (ha : d148336 q = 1) (hb : d170653 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148336, d170653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148336, d170653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148337 q = 1) (hb : d170654 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148337, d170654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148337, d170654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d148338 q = 1) (hb : d170655 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148338, d170655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148338, d170655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148341 q = 1) (hb : d170658 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148341, d170658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37385 q ha hb
    | true =>
      simp only [d148341, d170658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37386 q ha hb
  have h21 (q : Pattern) (ha : d148342 q = 1) (hb : d170659 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148342, d170659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148342, d170659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d148343 q = 1) (hb : d170660 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148343, d170660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148343, d170660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148346 q = 1) (hb : d170663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148346, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37387 q ha hb
    | true =>
      simp only [d148346, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37388 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d148259 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d148347 q = 1) (hb : d170664 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d148347, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d148349 q = 1) (hb : d170666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148349, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37389 q ha hb
    | true =>
      simp only [d148349, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d148350 q = 1) (hb : d170667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148350, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d148350, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d148351 q = 1) (hb : d170668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d148351, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d148352 q = 1) (hb : d170669 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148352, d170669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d148352, d170669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d148353 q = 1) (hb : d170670 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148353, d170670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148353, d170670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d148354 q = 1) (hb : d170671 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148354, d170671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148354, d170671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro37391 (p : Pattern) (ha : d148366 p = 1) (hb : d170683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148356 q = 1) (hb : d170673 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148356, d170673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37379 q ha hb
    | true =>
      simp only [d148356, d170673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37366 q ha hb
  have h2 (q : Pattern) (ha : d148357 q = 1) (hb : d170674 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148357, d170674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148357, d170674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148358 q = 1) (hb : d170675 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148358, d170675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148358, d170675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148359 q = 1) (hb : d170676 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148359, d170676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148359, d170676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148360 q = 1) (hb : d170677 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148360, d170677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148360, d170677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148361 q = 1) (hb : d170678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148361, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37366 q ha hb
    | true =>
      simp only [d148361, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148362 q = 1) (hb : d170679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148362, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148362, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148363 q = 1) (hb : d170680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148363, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148363, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148364 q = 1) (hb : d170681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148364, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148364, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148365 q = 1) (hb : d170682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148365, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148365, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148366 q = 1) (hb : d170683 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148366, d170683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148366, d170683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37392 (p : Pattern) (ha : d148372 p = 1) (hb : d170689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148361 q = 1) (hb : d170678 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148361, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37366 q ha hb
    | true =>
      simp only [d148361, d170678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148362 q = 1) (hb : d170679 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148362, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148362, d170679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148363 q = 1) (hb : d170680 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148363, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148363, d170680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148364 q = 1) (hb : d170681 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148364, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148364, d170681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148365 q = 1) (hb : d170682 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148365, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148365, d170682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148367 q = 1) (hb : d170684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148367, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37369 q ha hb
    | true =>
      simp only [d148367, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148368 q = 1) (hb : d170685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148368, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148368, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148369 q = 1) (hb : d170686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148369, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148369, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148370 q = 1) (hb : d170687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148370, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148370, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148371 q = 1) (hb : d170688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148371, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148371, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148372 q = 1) (hb : d170689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148372, d170689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148372, d170689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro37393 (p : Pattern) (ha : d148379 p = 1) (hb : d170696 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148346 q = 1) (hb : d170663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148346, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37387 q ha hb
    | true =>
      simp only [d148346, d170663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37388 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148259 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148347 q = 1) (hb : d170664 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148347, d170664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148349 q = 1) (hb : d170666 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148349, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37389 q ha hb
    | true =>
      simp only [d148349, d170666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148350 q = 1) (hb : d170667 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148350, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148350, d170667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148351 q = 1) (hb : d170668 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148351, d170668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148377 q = 1) (hb : d170694 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148377, d170694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148377, d170694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148378 q = 1) (hb : d170695 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148378, d170695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148378, d170695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148379 q = 1) (hb : d170696 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148379, d170696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148379, d170696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37394 (p : Pattern) (ha : d148381 p = 1) (hb : d170698 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148367 q = 1) (hb : d170684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148367, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37369 q ha hb
    | true =>
      simp only [d148367, d170684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148368 q = 1) (hb : d170685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148368, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148368, d170685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148369 q = 1) (hb : d170686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148369, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148369, d170686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148370 q = 1) (hb : d170687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148370, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148370, d170687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148371 q = 1) (hb : d170688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148371, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148371, d170688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148381 q = 1) (hb : d170698 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148381, d170698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148381, d170698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37395 (p : Pattern) (ha : d22957 p = 1) (hb : d148414 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22952 q = 1) (hb : d148409 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22952, d148409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22952, d148409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29859 q ha hb
  have h2 (q : Pattern) (ha : d22699 q = 1) (hb : d148217 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22699, d148217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29859 q ha hb
    | true =>
      simp only [d22699, d148217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22953 q = 1) (hb : d148410 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22953, d148410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22953, d148410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22700 q = 1) (hb : d148218 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22700, d148218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22700, d148218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22954 q = 1) (hb : d148411 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22954, d148411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22954, d148411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22955 q = 1) (hb : d148412 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22955, d148412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22955, d148412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22956 q = 1) (hb : d148413 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22956, d148413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22956, d148413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22957 q = 1) (hb : d148414 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22957, d148414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22957, d148414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37396 (p : Pattern) (ha : d148390 p = 1) (hb : d170705 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17369 q = 1) (hb : d128031 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17369, d128031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
  have h2 (q : Pattern) (ha : d10343 q = 1) (hb : d101664 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23366 q ha hb
    | true =>
      simp only [d10343, d101664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17370 q = 1) (hb : d128032 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17370, d128032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10345 q = 1) (hb : d101666 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10345, d101666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17371 q = 1) (hb : d128033 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17371, d128033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17372 q = 1) (hb : d128034 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17372, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17372, d128034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d128041 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d148389 q = 1) (hb : d170704 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148389, d170704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d148389, d170704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h10 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d15770 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d15770, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148390 q = 1) (hb : d170705 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148390, d170705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148390, d170705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q hb ha
  exact h17 p ha hb
theorem andIntro37397 (p : Pattern) (ha : d148395 p = 1) (hb : d170709 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13813 q = 1) (hb : d113965 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13813, d113965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
  have h2 (q : Pattern) (ha : d10353 q = 1) (hb : d101674 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23367 q ha hb
    | true =>
      simp only [d10353, d101674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d13814 q = 1) (hb : d113966 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13814, d113966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10355 q = 1) (hb : d101676 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10355, d101676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d13815 q = 1) (hb : d113967 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d13815, d113967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d13816 q = 1) (hb : d113968 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d13816, d113968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d15770 q = 1) (hb : d113973 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15770, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d15770, d113973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d13817 q = 1) (hb : d113969 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
  have h10 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13818 q = 1) (hb : d113970 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13819 q = 1) (hb : d113971 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13820 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22937 q = 1) (hb : d148394 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d148394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22937, d148394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d148395 q = 1) (hb : d170709 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148395, d170709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
    | true =>
      simp only [d148395, d170709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37398 (p : Pattern) (ha : d148405 p = 1) (hb : d170715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d17376 q = 1) (hb : d128038 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d17376, d128038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
  have h2 (q : Pattern) (ha : d10364 q = 1) (hb : d101685 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23369 q ha hb
    | true =>
      simp only [d10364, d101685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d17377 q = 1) (hb : d128039 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d17377, d128039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d10366 q = 1) (hb : d101687 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10366, d101687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d17378 q = 1) (hb : d128040 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d17378, d128040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d17379 q = 1) (hb : d128041 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d17379, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d17379, d128041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d148403 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d148404 q = 1) (hb : d170714 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d148404, d170714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d148404, d170714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d13817 q = 1) (hb : d113969 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13817, d113969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
  have h10 (q : Pattern) (ha : d13678 q = 1) (hb : d113868 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29873 q ha hb
    | true =>
      simp only [d13678, d113868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h11 (q : Pattern) (ha : d13818 q = 1) (hb : d113970 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d13818, d113970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d13679 q = 1) (hb : d113869 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d13679, d113869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d13819 q = 1) (hb : d113971 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d13819, d113971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d13820 q = 1) (hb : d113972 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d13820, d113972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22937 q = 1) (hb : d148394 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22937, d148394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d22937, d148394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h16 (q : Pattern) (ha : d148405 q = 1) (hb : d170715 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d148405, d170715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148405, d170715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  exact h16 p ha hb
theorem andIntro37399 (p : Pattern) (ha : d148420 p = 1) (hb : d170724 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148388 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148391 q = 1) (hb : d170706 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148391, d170706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148391, d170706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37396 q ha hb
  have h3 (q : Pattern) (ha : d148392 q = 1) (hb : d170707 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148392, d170707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148392, d170707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148393 q = 1) (hb : d170708 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148393, d170708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148393, d170708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148396 q = 1) (hb : d170710 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148396, d170710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37396 q ha hb
    | true =>
      simp only [d148396, d170710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37397 q ha hb
  have h6 (q : Pattern) (ha : d148397 q = 1) (hb : d170711 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148397, d170711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148397, d170711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148398 q = 1) (hb : d170712 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148398, d170712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148398, d170712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148399 q = 1) (hb : d170713 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148399, d170713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148399, d170713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148406 q = 1) (hb : d170716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37396 q ha hb
    | true =>
      simp only [d148406, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
  have h10 (q : Pattern) (ha : d148407 q = 1) (hb : d170717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148408 q = 1) (hb : d170718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d148415 q = 1) (hb : d170719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
    | true =>
      simp only [d148415, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37395 q hb ha
  have h13 (q : Pattern) (ha : d148416 q = 1) (hb : d170720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148417 q = 1) (hb : d170721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148418 q = 1) (hb : d170722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148418, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148419 q = 1) (hb : d170723 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148419, d170723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148419, d170723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148420 q = 1) (hb : d170724 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148420, d170724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148420, d170724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h17 p ha hb
theorem andIntro37400 (p : Pattern) (ha : d148425 p = 1) (hb : d170729 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d170716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37396 q ha hb
    | true =>
      simp only [d148406, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d170717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d170718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d170719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
    | true =>
      simp only [d148415, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37395 q hb ha
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d170720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d170721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d170722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148423 q = 1) (hb : d170727 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148423, d170727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148423, d170727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d148424 q = 1) (hb : d170728 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148424, d170728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148424, d170728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148425 q = 1) (hb : d170729 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148425, d170729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148425, d170729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro37401 (p : Pattern) (ha : d148431 p = 1) (hb : d170735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148421 q = 1) (hb : d170725 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148421, d170725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37399 q ha hb
    | true =>
      simp only [d148421, d170725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148422 q = 1) (hb : d170726 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148422, d170726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148422, d170726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148426 q = 1) (hb : d170730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148426, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37400 q ha hb
    | true =>
      simp only [d148426, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148427 q = 1) (hb : d170731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148427, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148427, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148428 q = 1) (hb : d170732 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148428, d170732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148428, d170732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148429 q = 1) (hb : d170733 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148429, d170733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148429, d170733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148430 q = 1) (hb : d170734 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148430, d170734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148430, d170734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148431 q = 1) (hb : d170735 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148431, d170735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148431, d170735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37402 (p : Pattern) (ha : d22976 p = 1) (hb : d148433 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d22943 q = 1) (hb : d148400 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22943, d148400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d22943, d148400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
  have h2 (q : Pattern) (ha : d22688 q = 1) (hb : d148206 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28298 q ha hb
    | true =>
      simp only [d22688, d148206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d22944 q = 1) (hb : d148401 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22944, d148401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d22944, d148401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d22689 q = 1) (hb : d148207 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d22689, d148207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d22945 q = 1) (hb : d148402 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d22945, d148402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d22945, d148402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d22946 q = 1) (hb : d148403 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d22946, d148403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d22946, d148403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d22975 q = 1) (hb : d148432 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d22975, d148432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d22975, d148432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d15790 q = 1) (hb : d123743 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15790, d123743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
  have h9 (q : Pattern) (ha : d10412 q = 1) (hb : d101733 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23361 q ha hb
    | true =>
      simp only [d10412, d101733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h10 (q : Pattern) (ha : d15791 q = 1) (hb : d123744 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d15791, d123744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d10414 q = 1) (hb : d101735 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d10414, d101735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d15792 q = 1) (hb : d123745 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15792, d123745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d15793 q = 1) (hb : d123746 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d15793, d123746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d15794 q = 1) (hb : d123747 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d15794, d123747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d22976 q = 1) (hb : d148433 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d22976, d148433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d22976, d148433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37403 (p : Pattern) (ha : d148439 p = 1) (hb : d170741 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148434 q = 1) (hb : d170736 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
    | true =>
      simp only [d148434, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37402 q hb ha
  have h2 (q : Pattern) (ha : d148435 q = 1) (hb : d170737 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148436 q = 1) (hb : d170738 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148437 q = 1) (hb : d170739 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148437, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148438 q = 1) (hb : d170740 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148438, d170740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148438, d170740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148439 q = 1) (hb : d170741 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148439, d170741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148439, d170741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37404 (p : Pattern) (ha : d148445 p = 1) (hb : d170747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148426 q = 1) (hb : d170730 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148426, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37400 q ha hb
    | true =>
      simp only [d148426, d170730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148427 q = 1) (hb : d170731 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148427, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148427, d170731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d170742 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37403 q ha hb
    | true =>
      simp only [d148440, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d170743 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148442 q = 1) (hb : d170744 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148442, d170744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148442, d170744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148443 q = 1) (hb : d170745 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148443, d170745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148443, d170745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148444 q = 1) (hb : d170746 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148444, d170746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148444, d170746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148445 q = 1) (hb : d170747 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148445, d170747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148445, d170747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37405 (p : Pattern) (ha : d148467 p = 1) (hb : d170755 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d170716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37396 q ha hb
    | true =>
      simp only [d148406, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d170717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d170718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d170719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
    | true =>
      simp only [d148415, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37395 q hb ha
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d170720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d170721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d170722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148462 q = 1) (hb : d170750 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148462, d170750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
    | true =>
      simp only [d148462, d170750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro29903 q hb ha
  have h9 (q : Pattern) (ha : d148463 q = 1) (hb : d170751 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148463, d170751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148463, d170751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148464 q = 1) (hb : d170752 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148464, d170752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148464, d170752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148465 q = 1) (hb : d170753 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148465, d170753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148465, d170753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148466 q = 1) (hb : d170754 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148466, d170754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148466, d170754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148467 q = 1) (hb : d170755 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148467, d170755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148467, d170755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37406 (p : Pattern) (ha : d148473 p = 1) (hb : d170761 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148468 q = 1) (hb : d170756 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148468, d170756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37405 q ha hb
    | true =>
      simp only [d148468, d170756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148469 q = 1) (hb : d170757 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148469, d170757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148469, d170757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148470 q = 1) (hb : d170758 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148470, d170758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148470, d170758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148471 q = 1) (hb : d170759 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148471, d170759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148471, d170759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148472 q = 1) (hb : d170760 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148472, d170760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148472, d170760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148473 q = 1) (hb : d170761 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148473, d170761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148473, d170761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37407 (p : Pattern) (ha : d148479 p = 1) (hb : d170767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148446 q = 1) (hb : d170748 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148446, d170748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37401 q ha hb
    | true =>
      simp only [d148446, d170748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37404 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148459 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d170749 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d170749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148460, d170749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d148474 q = 1) (hb : d170762 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148474, d170762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37406 q ha hb
    | true =>
      simp only [d148474, d170762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148475 q = 1) (hb : d170763 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148475, d170763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148475, d170763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148476 q = 1) (hb : d170764 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d170764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d170764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148477 q = 1) (hb : d170765 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d170765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d170765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148478 q = 1) (hb : d170766 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d170766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d170766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148479 q = 1) (hb : d170767 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d170767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d170767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro37408 (p : Pattern) (ha : d148458 p = 1) (hb : d170772 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148440 q = 1) (hb : d170742 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37403 q ha hb
    | true =>
      simp only [d148440, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148441 q = 1) (hb : d170743 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148455 q = 1) (hb : d170769 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148455, d170769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148455, d170769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148456 q = 1) (hb : d170770 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148456, d170770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148456, d170770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148457 q = 1) (hb : d170771 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148457, d170771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148457, d170771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148458 q = 1) (hb : d170772 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148458, d170772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148458, d170772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37409 (p : Pattern) (ha : d148486 p = 1) (hb : d170778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148481 q = 1) (hb : d170773 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148481, d170773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37408 q ha hb
    | true =>
      simp only [d148481, d170773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148482 q = 1) (hb : d170774 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148482, d170774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148482, d170774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148483 q = 1) (hb : d170775 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148483, d170775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148483, d170775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148484 q = 1) (hb : d170776 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148484, d170776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148484, d170776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148485 q = 1) (hb : d170777 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148485, d170777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148485, d170777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148486 q = 1) (hb : d170778 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148486, d170778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148486, d170778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37410 (p : Pattern) (ha : d148492 p = 1) (hb : d170784 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148255 q = 1) (hb : d170575 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148255, d170575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148255, d170575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37367 q ha hb
  have h2 (q : Pattern) (ha : d148256 q = 1) (hb : d170576 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148256, d170576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148256, d170576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148265 q = 1) (hb : d170585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148265, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37367 q ha hb
    | true =>
      simp only [d148265, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37370 q ha hb
  have h4 (q : Pattern) (ha : d148266 q = 1) (hb : d170586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148266, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148266, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148267 q = 1) (hb : d170587 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148267, d170587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148267, d170587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148355 q = 1) (hb : d170672 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d170672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37382 q ha hb
    | true =>
      simp only [d148355, d170672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37390 q ha hb
  have h7 (q : Pattern) (ha : d148373 q = 1) (hb : d170690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148373, d170690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37391 q ha hb
    | true =>
      simp only [d148373, d170690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37392 q ha hb
  have h8 (q : Pattern) (ha : d148374 q = 1) (hb : d170691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d170691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148374, d170691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148375 q = 1) (hb : d170692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d170692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148375, d170692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d148376 q = 1) (hb : d170693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d170693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148376, d170693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148380 q = 1) (hb : d170697 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d170697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148380, d170697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37393 q ha hb
  have h12 (q : Pattern) (ha : d148382 q = 1) (hb : d170699 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148382, d170699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148382, d170699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37394 q ha hb
  have h13 (q : Pattern) (ha : d148383 q = 1) (hb : d170700 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d170700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d148383, d170700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148384 q = 1) (hb : d170701 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d170701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148384, d170701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d148385 q = 1) (hb : d170702 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d170702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d148385, d170702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d148386 q = 1) (hb : d170703 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d170703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148386, d170703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148480 q = 1) (hb : d170768 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d170768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148480, d170768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37407 q ha hb
  have h18 (q : Pattern) (ha : d148487 q = 1) (hb : d170779 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148487, d170779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148487, d170779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37409 q ha hb
  have h19 (q : Pattern) (ha : d148488 q = 1) (hb : d170780 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d170780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148488, d170780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d148489 q = 1) (hb : d170781 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d170781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d148489, d170781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d148490 q = 1) (hb : d170782 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d170782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d148490, d170782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d148491 q = 1) (hb : d170783 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d170783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d148491, d170783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d148492 q = 1) (hb : d170784 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d170784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148492, d170784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro37411 (p : Pattern) (ha : d148498 p = 1) (hb : d170790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d170785 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d170785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d170785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37410 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d170786 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d170786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d170786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d170787 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d170787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d170787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d170788 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d170788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d170788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d170789 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d170789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d170789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d170790 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d170790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d170790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37412 (p : Pattern) (ha : d148504 p = 1) (hb : d170796 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d147261 q = 1) (hb : d169789 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147261, d169789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37156 q ha hb
    | true =>
      simp only [d147261, d169789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37198 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147500 q = 1) (hb : d170005 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147500, d170005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147500, d170005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37245 q ha hb
  have h3 (q : Pattern) (ha : d147501 q = 1) (hb : d170006 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147501, d170006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d147501, d170006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147858 q = 1) (hb : d170270 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d147858, d170270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147858, d170270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37302 q ha hb
  have h5 (q : Pattern) (ha : d147859 q = 1) (hb : d170271 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d147859, d170271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147859, d170271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147860 q = 1) (hb : d170272 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d147860, d170272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147860, d170272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148199 q = 1) (hb : d170534 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148199, d170534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148199, d170534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37358 q ha hb
  have h8 (q : Pattern) (ha : d148200 q = 1) (hb : d170535 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148200, d170535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148200, d170535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148201 q = 1) (hb : d170536 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148201, d170536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148201, d170536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148202 q = 1) (hb : d170537 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148202, d170537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148202, d170537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148499 q = 1) (hb : d170791 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d148499, d170791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148499, d170791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37411 q ha hb
  have h12 (q : Pattern) (ha : d148500 q = 1) (hb : d170792 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d148500, d170792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148500, d170792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148501 q = 1) (hb : d170793 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d148501, d170793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148501, d170793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d148502 q = 1) (hb : d170794 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d148502, d170794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148502, d170794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d148503 q = 1) (hb : d170795 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d148503, d170795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148503, d170795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d148504 q = 1) (hb : d170796 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d148504, d170796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148504, d170796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro37413 (p : Pattern) (ha : d148510 p = 1) (hb : d170802 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148505 q = 1) (hb : d170797 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d148505, d170797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37412 q ha hb
    | true =>
      simp only [d148505, d170797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148506 q = 1) (hb : d170798 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d148506, d170798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148506, d170798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148507 q = 1) (hb : d170799 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d148507, d170799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148507, d170799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148508 q = 1) (hb : d170800 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d148508, d170800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148508, d170800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148509 q = 1) (hb : d170801 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d148509, d170801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148509, d170801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148510 q = 1) (hb : d170802 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d148510, d170802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148510, d170802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37414 (p : Pattern) (ha : d148516 p = 1) (hb : d170808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148511 q = 1) (hb : d170803 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d148511, d170803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37413 q ha hb
    | true =>
      simp only [d148511, d170803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148512 q = 1) (hb : d170804 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d148512, d170804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148512, d170804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148513 q = 1) (hb : d170805 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d148513, d170805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148513, d170805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148514 q = 1) (hb : d170806 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d148514, d170806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148514, d170806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148515 q = 1) (hb : d170807 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d148515, d170807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148515, d170807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148516 q = 1) (hb : d170808 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d148516, d170808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148516, d170808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37415 (p : Pattern) (ha : d148522 p = 1) (hb : d170814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148517 q = 1) (hb : d170809 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d148517, d170809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37414 q ha hb
    | true =>
      simp only [d148517, d170809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148518 q = 1) (hb : d170810 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d148518, d170810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148518, d170810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148519 q = 1) (hb : d170811 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d148519, d170811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148519, d170811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148520 q = 1) (hb : d170812 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d148520, d170812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148520, d170812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148521 q = 1) (hb : d170813 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d148521, d170813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148521, d170813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148522 q = 1) (hb : d170814 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d148522, d170814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148522, d170814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37416 (p : Pattern) (ha : d148528 p = 1) (hb : d170820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148523 q = 1) (hb : d170815 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d148523, d170815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37415 q ha hb
    | true =>
      simp only [d148523, d170815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148524 q = 1) (hb : d170816 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d148524, d170816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148524, d170816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148525 q = 1) (hb : d170817 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d148525, d170817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148525, d170817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148526 q = 1) (hb : d170818 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d148526, d170818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148526, d170818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148527 q = 1) (hb : d170819 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d148527, d170819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148527, d170819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148528 q = 1) (hb : d170820 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d148528, d170820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148528, d170820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37417 (p : Pattern) (ha : d148534 p = 1) (hb : d170826 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148529 q = 1) (hb : d170821 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d148529, d170821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37416 q ha hb
    | true =>
      simp only [d148529, d170821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148530 q = 1) (hb : d170822 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d148530, d170822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148530, d170822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148531 q = 1) (hb : d170823 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d148531, d170823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148531, d170823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148532 q = 1) (hb : d170824 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d148532, d170824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148532, d170824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148533 q = 1) (hb : d170825 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d148533, d170825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148533, d170825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148534 q = 1) (hb : d170826 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d148534, d170826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148534, d170826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37418 (p : Pattern) (ha : d148540 p = 1) (hb : d170832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148535 q = 1) (hb : d170827 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d148535, d170827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37417 q ha hb
    | true =>
      simp only [d148535, d170827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148536 q = 1) (hb : d170828 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d148536, d170828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148536, d170828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148537 q = 1) (hb : d170829 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d148537, d170829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148537, d170829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148538 q = 1) (hb : d170830 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d148538, d170830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148538, d170830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148539 q = 1) (hb : d170831 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d148539, d170831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148539, d170831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148540 q = 1) (hb : d170832 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d148540, d170832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148540, d170832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37419 (p : Pattern) (ha : d148546 p = 1) (hb : d170838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148541 q = 1) (hb : d170833 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d148541, d170833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37418 q ha hb
    | true =>
      simp only [d148541, d170833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148542 q = 1) (hb : d170834 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d148542, d170834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148542, d170834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d148543 q = 1) (hb : d170835 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d148543, d170835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148543, d170835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148544 q = 1) (hb : d170836 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d148544, d170836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148544, d170836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d148545 q = 1) (hb : d170837 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d148545, d170837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148545, d170837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d148546 q = 1) (hb : d170838 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d148546, d170838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148546, d170838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro37420 (p : Pattern) (ha : d163447 p = 1) (hb : d169395 p = 1) : d170841 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d49 q = 1) (hb : d169395 q = 1) : d49 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14001 q = 1) (hb : d169395 q = 1) : d169418 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14001, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36819 q ha hb
    | true =>
      simp only [d14001, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14057 q = 1) (hb : d169395 q = 1) : d169473 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14057, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14057, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d14058 q = 1) (hb : d169395 q = 1) : d169474 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14058, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d14058, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d14059 q = 1) (hb : d169395 q = 1) : d169475 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14059, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14059, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d14060 q = 1) (hb : d169395 q = 1) : d169476 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14060, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14060, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d163447 q = 1) (hb : d169395 q = 1) : d170841 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163447, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163447, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro37421 (p : Pattern) (ha : d163457 p = 1) (hb : d169395 p = 1) : d170851 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d83 q = 1) (hb : d169395 q = 1) : d83 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d14033 q = 1) (hb : d169395 q = 1) : d169449 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14033, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36824 q ha hb
    | true =>
      simp only [d14033, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163453 q = 1) (hb : d169395 q = 1) : d170847 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163453, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163453, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163454 q = 1) (hb : d169395 q = 1) : d170848 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163454, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163454, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163455 q = 1) (hb : d169395 q = 1) : d170849 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163455, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163455, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163456 q = 1) (hb : d169395 q = 1) : d170850 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163456, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163456, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d163457 q = 1) (hb : d169395 q = 1) : d170851 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163457, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163457, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro37422 (p : Pattern) (ha : d163463 p = 1) (hb : d169395 p = 1) : d170857 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14062 q = 1) (hb : d169395 q = 1) : d169478 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14062, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36827 q ha hb
    | true =>
      simp only [d14062, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36828 q ha hb
  have h2 (q : Pattern) (ha : d14063 q = 1) (hb : d169395 q = 1) : d169479 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14063, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14063, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163445 q = 1) (hb : d169395 q = 1) : d170839 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163445, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163445, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163446 q = 1) (hb : d169395 q = 1) : d170840 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163446, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163446, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163448 q = 1) (hb : d169395 q = 1) : d170842 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163448, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163448, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37420 q ha hb
  have h6 (q : Pattern) (ha : d163449 q = 1) (hb : d169395 q = 1) : d170843 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163449, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163449, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163450 q = 1) (hb : d169395 q = 1) : d170844 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163450, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163450, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163451 q = 1) (hb : d169395 q = 1) : d170845 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163451, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163451, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163452 q = 1) (hb : d169395 q = 1) : d170846 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163452, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163452, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163458 q = 1) (hb : d169395 q = 1) : d170852 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163458, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163458, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37421 q ha hb
  have h11 (q : Pattern) (ha : d163459 q = 1) (hb : d169395 q = 1) : d170853 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163459, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163459, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163460 q = 1) (hb : d169395 q = 1) : d170854 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163460, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163460, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163461 q = 1) (hb : d169395 q = 1) : d170855 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163461, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163461, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163462 q = 1) (hb : d169395 q = 1) : d170856 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163462, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163462, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163463 q = 1) (hb : d169395 q = 1) : d170857 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163463, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163463, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37423 (p : Pattern) (ha : d163469 p = 1) (hb : d169395 p = 1) : d170863 p = 1 := by
  have h0 (q : Pattern) (ha : d53652 q = 1) (hb : d169395 q = 1) : d53652 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d163464 q = 1) (hb : d169395 q = 1) : d170858 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163464, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163464, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37422 q ha hb
  have h3 (q : Pattern) (ha : d163465 q = 1) (hb : d169395 q = 1) : d170859 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163465, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163465, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163466 q = 1) (hb : d169395 q = 1) : d170860 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163466, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163466, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163467 q = 1) (hb : d169395 q = 1) : d170861 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163467, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163467, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163468 q = 1) (hb : d169395 q = 1) : d170862 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163468, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163468, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d163469 q = 1) (hb : d169395 q = 1) : d170863 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163469, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163469, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro37424 (p : Pattern) (ha : d163472 p = 1) (hb : d169395 p = 1) : d170866 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14235 q = 1) (hb : d169395 q = 1) : d169617 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14235, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36855 q ha hb
    | true =>
      simp only [d14235, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36856 q ha hb
  have h2 (q : Pattern) (ha : d14236 q = 1) (hb : d169395 q = 1) : d169618 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14236, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14236, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14237 q = 1) (hb : d169395 q = 1) : d169619 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14237, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14237, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14238 q = 1) (hb : d169395 q = 1) : d169620 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14238, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14238, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14239 q = 1) (hb : d169395 q = 1) : d169621 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14239, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14239, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163472 q = 1) (hb : d169395 q = 1) : d170866 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163472, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163472, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37425 (p : Pattern) (ha : d163483 p = 1) (hb : d169395 p = 1) : d170877 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163478 q = 1) (hb : d169395 q = 1) : d170872 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163478, d170872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36887 q ha hb
    | true =>
      simp only [d163478, d170872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36862 q ha hb
  have h2 (q : Pattern) (ha : d163479 q = 1) (hb : d169395 q = 1) : d170873 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163479, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163479, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163480 q = 1) (hb : d169395 q = 1) : d170874 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163480, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163480, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163481 q = 1) (hb : d169395 q = 1) : d170875 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163481, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163481, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163482 q = 1) (hb : d169395 q = 1) : d170876 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163482, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163482, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163483 q = 1) (hb : d169395 q = 1) : d170877 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163483, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163483, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37426 (p : Pattern) (ha : d163489 p = 1) (hb : d169395 p = 1) : d170883 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14241 q = 1) (hb : d169395 q = 1) : d169623 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14241, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36854 q ha hb
    | true =>
      simp only [d14241, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36857 q ha hb
  have h2 (q : Pattern) (ha : d14242 q = 1) (hb : d169395 q = 1) : d169624 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14242, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14242, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163470 q = 1) (hb : d169395 q = 1) : d170864 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163470, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163470, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163471 q = 1) (hb : d169395 q = 1) : d170865 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163471, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163471, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163473 q = 1) (hb : d169395 q = 1) : d170867 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163473, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163473, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37424 q ha hb
  have h6 (q : Pattern) (ha : d163474 q = 1) (hb : d169395 q = 1) : d170868 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163474, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163474, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163475 q = 1) (hb : d169395 q = 1) : d170869 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163475, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163475, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163476 q = 1) (hb : d169395 q = 1) : d170870 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163476, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163476, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163477 q = 1) (hb : d169395 q = 1) : d170871 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163477, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163477, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163484 q = 1) (hb : d169395 q = 1) : d170878 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163484, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163484, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37425 q ha hb
  have h11 (q : Pattern) (ha : d163485 q = 1) (hb : d169395 q = 1) : d170879 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163485, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163485, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163486 q = 1) (hb : d169395 q = 1) : d170880 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163486, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163486, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163487 q = 1) (hb : d169395 q = 1) : d170881 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163487, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163487, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163488 q = 1) (hb : d169395 q = 1) : d170882 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163488, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163488, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163489 q = 1) (hb : d169395 q = 1) : d170883 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163489, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163489, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37427 (p : Pattern) (ha : d163495 p = 1) (hb : d169395 p = 1) : d170889 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163490 q = 1) (hb : d169395 q = 1) : d170884 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163490, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163490, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37426 q ha hb
  have h2 (q : Pattern) (ha : d163491 q = 1) (hb : d169395 q = 1) : d170885 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163491, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163491, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163492 q = 1) (hb : d169395 q = 1) : d170886 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163492, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163492, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163493 q = 1) (hb : d169395 q = 1) : d170887 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163493, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163493, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163494 q = 1) (hb : d169395 q = 1) : d170888 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163494, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163494, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163495 q = 1) (hb : d169395 q = 1) : d170889 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163495, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163495, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37428 (p : Pattern) (ha : d163499 p = 1) (hb : d169395 p = 1) : d170893 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14502 q = 1) (hb : d169395 q = 1) : d169825 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14502, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36898 q ha hb
    | true =>
      simp only [d14502, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36899 q ha hb
  have h2 (q : Pattern) (ha : d14503 q = 1) (hb : d169395 q = 1) : d169826 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14503, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14503, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14504 q = 1) (hb : d169395 q = 1) : d169827 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14504, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14504, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14505 q = 1) (hb : d169395 q = 1) : d169828 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14505, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14505, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14506 q = 1) (hb : d169395 q = 1) : d169829 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14506, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14506, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163499 q = 1) (hb : d169395 q = 1) : d170893 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163499, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163499, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37429 (p : Pattern) (ha : d163510 p = 1) (hb : d169395 p = 1) : d170904 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163505 q = 1) (hb : d169395 q = 1) : d170899 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163505, d170899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36932 q ha hb
    | true =>
      simp only [d163505, d170899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36906 q ha hb
  have h2 (q : Pattern) (ha : d163506 q = 1) (hb : d169395 q = 1) : d170900 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163506, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163506, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163507 q = 1) (hb : d169395 q = 1) : d170901 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163507, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163507, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163508 q = 1) (hb : d169395 q = 1) : d170902 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163508, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163508, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163509 q = 1) (hb : d169395 q = 1) : d170903 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163509, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163509, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163510 q = 1) (hb : d169395 q = 1) : d170904 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163510, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163510, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37430 (p : Pattern) (ha : d163516 p = 1) (hb : d169395 p = 1) : d170910 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14508 q = 1) (hb : d169395 q = 1) : d169831 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14508, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36897 q ha hb
    | true =>
      simp only [d14508, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36900 q ha hb
  have h2 (q : Pattern) (ha : d14509 q = 1) (hb : d169395 q = 1) : d169832 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14509, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14509, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163497 q = 1) (hb : d169395 q = 1) : d170891 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163497, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163497, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163498 q = 1) (hb : d169395 q = 1) : d170892 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163498, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163498, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163500 q = 1) (hb : d169395 q = 1) : d170894 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163500, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163500, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37428 q ha hb
  have h6 (q : Pattern) (ha : d163501 q = 1) (hb : d169395 q = 1) : d170895 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163501, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163501, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163502 q = 1) (hb : d169395 q = 1) : d170896 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163502, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163502, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163503 q = 1) (hb : d169395 q = 1) : d170897 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163503, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163503, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163504 q = 1) (hb : d169395 q = 1) : d170898 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163504, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163504, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163511 q = 1) (hb : d169395 q = 1) : d170905 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163511, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163511, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37429 q ha hb
  have h11 (q : Pattern) (ha : d163512 q = 1) (hb : d169395 q = 1) : d170906 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163512, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163512, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163513 q = 1) (hb : d169395 q = 1) : d170907 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163513, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163513, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163514 q = 1) (hb : d169395 q = 1) : d170908 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163514, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163514, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163515 q = 1) (hb : d169395 q = 1) : d170909 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163515, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163515, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163516 q = 1) (hb : d169395 q = 1) : d170910 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163516, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163516, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37431 (p : Pattern) (ha : d163522 p = 1) (hb : d169395 p = 1) : d170916 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163517 q = 1) (hb : d169395 q = 1) : d170911 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163517, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163517, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37430 q ha hb
  have h2 (q : Pattern) (ha : d163518 q = 1) (hb : d169395 q = 1) : d170912 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163518, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163518, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163519 q = 1) (hb : d169395 q = 1) : d170913 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163519, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163519, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163520 q = 1) (hb : d169395 q = 1) : d170914 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163520, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163520, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163521 q = 1) (hb : d169395 q = 1) : d170915 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163521, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163521, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163522 q = 1) (hb : d169395 q = 1) : d170916 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163522, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163522, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37432 (p : Pattern) (ha : d163527 p = 1) (hb : d169395 p = 1) : d170921 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14809 q = 1) (hb : d169395 q = 1) : d170049 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d14809, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36948 q ha hb
    | true =>
      simp only [d14809, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36949 q ha hb
  have h2 (q : Pattern) (ha : d14810 q = 1) (hb : d169395 q = 1) : d170050 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d14810, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14810, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d14811 q = 1) (hb : d169395 q = 1) : d170051 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d14811, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d14811, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d14812 q = 1) (hb : d169395 q = 1) : d170052 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d14812, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14812, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d14813 q = 1) (hb : d169395 q = 1) : d170053 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d14813, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d14813, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163527 q = 1) (hb : d169395 q = 1) : d170921 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163527, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163527, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37433 (p : Pattern) (ha : d163534 p = 1) (hb : d169395 p = 1) : d170928 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15016 q = 1) (hb : d169395 q = 1) : d170195 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15016, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36984 q ha hb
    | true =>
      simp only [d15016, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36956 q ha hb
  have h2 (q : Pattern) (ha : d15017 q = 1) (hb : d169395 q = 1) : d170196 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15017, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15017, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15018 q = 1) (hb : d169395 q = 1) : d170197 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15018, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15018, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15025 q = 1) (hb : d169395 q = 1) : d170198 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15025, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36956 q ha hb
    | true =>
      simp only [d15025, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36986 q ha hb
  have h5 (q : Pattern) (ha : d15026 q = 1) (hb : d169395 q = 1) : d170199 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15026, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15026, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15027 q = 1) (hb : d169395 q = 1) : d170200 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15027, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15027, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15028 q = 1) (hb : d169395 q = 1) : d170201 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15028, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15028, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15043 q = 1) (hb : d169395 q = 1) : d170215 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15043, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36956 q ha hb
    | true =>
      simp only [d15043, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36957 q ha hb
  have h9 (q : Pattern) (ha : d15044 q = 1) (hb : d169395 q = 1) : d170216 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15044, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15044, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15045 q = 1) (hb : d169395 q = 1) : d170217 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15045, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15045, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15046 q = 1) (hb : d169395 q = 1) : d170218 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15046, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15046, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163533 q = 1) (hb : d169395 q = 1) : d170927 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163533, d170927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163533, d170927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163534 q = 1) (hb : d169395 q = 1) : d170928 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163534, d170928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163534, d170928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37434 (p : Pattern) (ha : d163540 p = 1) (hb : d169395 p = 1) : d170934 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163535 q = 1) (hb : d169395 q = 1) : d170929 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163535, d170929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37433 q ha hb
    | true =>
      simp only [d163535, d170929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163536 q = 1) (hb : d169395 q = 1) : d170930 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163536, d170930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163536, d170930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15049 q = 1) (hb : d169395 q = 1) : d170221 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15049, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36958 q ha hb
    | true =>
      simp only [d15049, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15050 q = 1) (hb : d169395 q = 1) : d170222 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15050, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15050, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163537 q = 1) (hb : d169395 q = 1) : d170931 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163537, d170931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163537, d170931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163538 q = 1) (hb : d169395 q = 1) : d170932 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163538, d170932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163538, d170932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163539 q = 1) (hb : d169395 q = 1) : d170933 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163539, d170933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163539, d170933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163540 q = 1) (hb : d169395 q = 1) : d170934 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163540, d170934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163540, d170934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37435 (p : Pattern) (ha : d163546 p = 1) (hb : d169395 p = 1) : d170940 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163541 q = 1) (hb : d169395 q = 1) : d170935 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163541, d170935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37434 q ha hb
    | true =>
      simp only [d163541, d170935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36959 q ha hb
  have h2 (q : Pattern) (ha : d163542 q = 1) (hb : d169395 q = 1) : d170936 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163542, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163542, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163543 q = 1) (hb : d169395 q = 1) : d170937 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163543, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163543, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163544 q = 1) (hb : d169395 q = 1) : d170938 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163544, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163544, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163545 q = 1) (hb : d169395 q = 1) : d170939 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163545, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163545, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163546 q = 1) (hb : d169395 q = 1) : d170940 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163546, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163546, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37436 (p : Pattern) (ha : d163552 p = 1) (hb : d169395 p = 1) : d170946 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d14815 q = 1) (hb : d169395 q = 1) : d170055 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d14815, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36947 q ha hb
    | true =>
      simp only [d14815, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro36950 q ha hb
  have h2 (q : Pattern) (ha : d14816 q = 1) (hb : d169395 q = 1) : d170056 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d14816, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d14816, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163525 q = 1) (hb : d169395 q = 1) : d170919 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163525, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163525, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163526 q = 1) (hb : d169395 q = 1) : d170920 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163526, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163526, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163528 q = 1) (hb : d169395 q = 1) : d170922 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163528, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163528, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37432 q ha hb
  have h6 (q : Pattern) (ha : d163529 q = 1) (hb : d169395 q = 1) : d170923 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163529, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163529, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163530 q = 1) (hb : d169395 q = 1) : d170924 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163530, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163530, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163531 q = 1) (hb : d169395 q = 1) : d170925 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163531, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163531, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163532 q = 1) (hb : d169395 q = 1) : d170926 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163532, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163532, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163547 q = 1) (hb : d169395 q = 1) : d170941 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163547, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163547, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37435 q ha hb
  have h11 (q : Pattern) (ha : d163548 q = 1) (hb : d169395 q = 1) : d170942 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163548, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163548, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163549 q = 1) (hb : d169395 q = 1) : d170943 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163549, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163549, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163550 q = 1) (hb : d169395 q = 1) : d170944 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163550, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163550, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163551 q = 1) (hb : d169395 q = 1) : d170945 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163551, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163551, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163552 q = 1) (hb : d169395 q = 1) : d170946 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163552, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163552, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37437 (p : Pattern) (ha : d163558 p = 1) (hb : d169395 p = 1) : d170952 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163553 q = 1) (hb : d169395 q = 1) : d170947 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163553, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163553, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37436 q ha hb
  have h2 (q : Pattern) (ha : d163554 q = 1) (hb : d169395 q = 1) : d170948 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163554, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163554, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163555 q = 1) (hb : d169395 q = 1) : d170949 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163555, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163555, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163556 q = 1) (hb : d169395 q = 1) : d170950 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163556, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163556, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163557 q = 1) (hb : d169395 q = 1) : d170951 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163557, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163557, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163558 q = 1) (hb : d169395 q = 1) : d170952 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163558, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163558, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37438 (p : Pattern) (ha : d163564 p = 1) (hb : d169395 p = 1) : d170958 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15202 q = 1) (hb : d169395 q = 1) : d170315 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15202, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37008 q ha hb
    | true =>
      simp only [d15202, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37009 q ha hb
  have h2 (q : Pattern) (ha : d15203 q = 1) (hb : d169395 q = 1) : d170316 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15203, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15203, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15204 q = 1) (hb : d169395 q = 1) : d170317 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15204, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15204, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15205 q = 1) (hb : d169395 q = 1) : d170318 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15205, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15205, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15206 q = 1) (hb : d169395 q = 1) : d170319 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15206, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15206, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163564 q = 1) (hb : d169395 q = 1) : d170958 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163564, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163564, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37439 (p : Pattern) (ha : d163571 p = 1) (hb : d169395 p = 1) : d170965 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15409 q = 1) (hb : d169395 q = 1) : d170459 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15409, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37043 q ha hb
    | true =>
      simp only [d15409, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
  have h2 (q : Pattern) (ha : d15410 q = 1) (hb : d169395 q = 1) : d170460 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15410, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15410, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15411 q = 1) (hb : d169395 q = 1) : d170461 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15411, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15411, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15418 q = 1) (hb : d169395 q = 1) : d170462 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15418, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
    | true =>
      simp only [d15418, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37045 q ha hb
  have h5 (q : Pattern) (ha : d15419 q = 1) (hb : d169395 q = 1) : d170463 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15419, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15419, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15420 q = 1) (hb : d169395 q = 1) : d170464 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15420, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15420, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15421 q = 1) (hb : d169395 q = 1) : d170465 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15421, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15421, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15436 q = 1) (hb : d169395 q = 1) : d170479 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15436, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37016 q ha hb
    | true =>
      simp only [d15436, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37017 q ha hb
  have h9 (q : Pattern) (ha : d15437 q = 1) (hb : d169395 q = 1) : d170480 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15437, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15437, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15438 q = 1) (hb : d169395 q = 1) : d170481 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15438, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15438, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15439 q = 1) (hb : d169395 q = 1) : d170482 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15439, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15439, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163570 q = 1) (hb : d169395 q = 1) : d170964 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163570, d170964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163570, d170964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163571 q = 1) (hb : d169395 q = 1) : d170965 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163571, d170965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163571, d170965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37440 (p : Pattern) (ha : d163577 p = 1) (hb : d169395 p = 1) : d170971 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163572 q = 1) (hb : d169395 q = 1) : d170966 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163572, d170966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37439 q ha hb
    | true =>
      simp only [d163572, d170966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163573 q = 1) (hb : d169395 q = 1) : d170967 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163573, d170967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163573, d170967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15442 q = 1) (hb : d169395 q = 1) : d170485 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15442, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37018 q ha hb
    | true =>
      simp only [d15442, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15443 q = 1) (hb : d169395 q = 1) : d170486 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15443, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15443, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163574 q = 1) (hb : d169395 q = 1) : d170968 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163574, d170968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163574, d170968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163575 q = 1) (hb : d169395 q = 1) : d170969 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163575, d170969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163575, d170969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163576 q = 1) (hb : d169395 q = 1) : d170970 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163576, d170970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163576, d170970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163577 q = 1) (hb : d169395 q = 1) : d170971 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163577, d170971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163577, d170971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37441 (p : Pattern) (ha : d163583 p = 1) (hb : d169395 p = 1) : d170977 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163578 q = 1) (hb : d169395 q = 1) : d170972 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163578, d170972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37440 q ha hb
    | true =>
      simp only [d163578, d170972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37019 q ha hb
  have h2 (q : Pattern) (ha : d163579 q = 1) (hb : d169395 q = 1) : d170973 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163579, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163579, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163580 q = 1) (hb : d169395 q = 1) : d170974 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163580, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163580, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163581 q = 1) (hb : d169395 q = 1) : d170975 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163581, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163581, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163582 q = 1) (hb : d169395 q = 1) : d170976 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163582, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163582, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163583 q = 1) (hb : d169395 q = 1) : d170977 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163583, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163583, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37442 (p : Pattern) (ha : d163589 p = 1) (hb : d169395 p = 1) : d170983 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15208 q = 1) (hb : d169395 q = 1) : d170321 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15208, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37007 q ha hb
    | true =>
      simp only [d15208, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37010 q ha hb
  have h2 (q : Pattern) (ha : d15209 q = 1) (hb : d169395 q = 1) : d170322 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15209, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15209, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163562 q = 1) (hb : d169395 q = 1) : d170956 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163562, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163562, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163563 q = 1) (hb : d169395 q = 1) : d170957 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163563, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163563, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163565 q = 1) (hb : d169395 q = 1) : d170959 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163565, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163565, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37438 q ha hb
  have h6 (q : Pattern) (ha : d163566 q = 1) (hb : d169395 q = 1) : d170960 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163566, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163566, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163567 q = 1) (hb : d169395 q = 1) : d170961 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163567, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163567, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163568 q = 1) (hb : d169395 q = 1) : d170962 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163568, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163568, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163569 q = 1) (hb : d169395 q = 1) : d170963 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163569, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163569, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163584 q = 1) (hb : d169395 q = 1) : d170978 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163584, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163584, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37441 q ha hb
  have h11 (q : Pattern) (ha : d163585 q = 1) (hb : d169395 q = 1) : d170979 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163585, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163585, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163586 q = 1) (hb : d169395 q = 1) : d170980 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163586, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163586, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163587 q = 1) (hb : d169395 q = 1) : d170981 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163587, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163587, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163588 q = 1) (hb : d169395 q = 1) : d170982 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163588, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163588, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163589 q = 1) (hb : d169395 q = 1) : d170983 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163589, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163589, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37443 (p : Pattern) (ha : d163595 p = 1) (hb : d169395 p = 1) : d170989 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163590 q = 1) (hb : d169395 q = 1) : d170984 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163590, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163590, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37442 q ha hb
  have h2 (q : Pattern) (ha : d163591 q = 1) (hb : d169395 q = 1) : d170985 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163591, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163591, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163592 q = 1) (hb : d169395 q = 1) : d170986 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163592, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163592, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163593 q = 1) (hb : d169395 q = 1) : d170987 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163593, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163593, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163594 q = 1) (hb : d169395 q = 1) : d170988 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163594, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163594, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163595 q = 1) (hb : d169395 q = 1) : d170989 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163595, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163595, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37444 (p : Pattern) (ha : d163602 p = 1) (hb : d169395 p = 1) : d170996 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15594 q = 1) (hb : d169395 q = 1) : d170579 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d15594, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37066 q ha hb
    | true =>
      simp only [d15594, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37067 q ha hb
  have h2 (q : Pattern) (ha : d15595 q = 1) (hb : d169395 q = 1) : d170580 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d15595, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15595, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15596 q = 1) (hb : d169395 q = 1) : d170581 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d15596, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d15596, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15597 q = 1) (hb : d169395 q = 1) : d170582 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d15597, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15597, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d15598 q = 1) (hb : d169395 q = 1) : d170583 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d15598, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15598, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163602 q = 1) (hb : d169395 q = 1) : d170996 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163602, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163602, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37445 (p : Pattern) (ha : d163609 p = 1) (hb : d169395 p = 1) : d171003 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15787 q = 1) (hb : d169395 q = 1) : d170716 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15787, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37101 q ha hb
    | true =>
      simp only [d15787, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
  have h2 (q : Pattern) (ha : d15788 q = 1) (hb : d169395 q = 1) : d170717 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15788, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15788, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15789 q = 1) (hb : d169395 q = 1) : d170718 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15789, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15789, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d15796 q = 1) (hb : d169395 q = 1) : d170719 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15796, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
    | true =>
      simp only [d15796, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37103 q ha hb
  have h5 (q : Pattern) (ha : d15797 q = 1) (hb : d169395 q = 1) : d170720 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15797, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15797, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d15798 q = 1) (hb : d169395 q = 1) : d170721 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15798, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15798, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d15799 q = 1) (hb : d169395 q = 1) : d170722 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15799, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d15799, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d15814 q = 1) (hb : d169395 q = 1) : d170736 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d15814, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37074 q ha hb
    | true =>
      simp only [d15814, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37075 q ha hb
  have h9 (q : Pattern) (ha : d15815 q = 1) (hb : d169395 q = 1) : d170737 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d15815, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15815, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d15816 q = 1) (hb : d169395 q = 1) : d170738 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d15816, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15816, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d15817 q = 1) (hb : d169395 q = 1) : d170739 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d15817, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d15817, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163608 q = 1) (hb : d169395 q = 1) : d171002 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d163608, d171002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163608, d171002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163609 q = 1) (hb : d169395 q = 1) : d171003 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d163609, d171003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163609, d171003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h13 p ha hb
theorem andIntro37446 (p : Pattern) (ha : d163615 p = 1) (hb : d169395 p = 1) : d171009 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163610 q = 1) (hb : d169395 q = 1) : d171004 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d163610, d171004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37445 q ha hb
    | true =>
      simp only [d163610, d171004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163611 q = 1) (hb : d169395 q = 1) : d171005 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d163611, d171005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163611, d171005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d15820 q = 1) (hb : d169395 q = 1) : d170742 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d15820, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37076 q ha hb
    | true =>
      simp only [d15820, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d15821 q = 1) (hb : d169395 q = 1) : d170743 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d15821, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d15821, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163612 q = 1) (hb : d169395 q = 1) : d171006 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d163612, d171006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163612, d171006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163613 q = 1) (hb : d169395 q = 1) : d171007 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d163613, d171007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163613, d171007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163614 q = 1) (hb : d169395 q = 1) : d171008 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d163614, d171008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163614, d171008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163615 q = 1) (hb : d169395 q = 1) : d171009 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d163615, d171009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163615, d171009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro37447 (p : Pattern) (ha : d163621 p = 1) (hb : d169395 p = 1) : d171015 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163616 q = 1) (hb : d169395 q = 1) : d171010 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d163616, d171010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37446 q ha hb
    | true =>
      simp only [d163616, d171010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37077 q ha hb
  have h2 (q : Pattern) (ha : d163617 q = 1) (hb : d169395 q = 1) : d171011 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d163617, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163617, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163618 q = 1) (hb : d169395 q = 1) : d171012 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d163618, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163618, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163619 q = 1) (hb : d169395 q = 1) : d171013 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d163619, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163619, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163620 q = 1) (hb : d169395 q = 1) : d171014 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d163620, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163620, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163621 q = 1) (hb : d169395 q = 1) : d171015 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d163621, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163621, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37448 (p : Pattern) (ha : d163627 p = 1) (hb : d169395 p = 1) : d171021 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d15600 q = 1) (hb : d169395 q = 1) : d170585 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d15600, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37065 q ha hb
    | true =>
      simp only [d15600, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37068 q ha hb
  have h2 (q : Pattern) (ha : d15601 q = 1) (hb : d169395 q = 1) : d170586 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d15601, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d15601, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163600 q = 1) (hb : d169395 q = 1) : d170994 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163600, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163600, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163601 q = 1) (hb : d169395 q = 1) : d170995 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163601, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163601, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163603 q = 1) (hb : d169395 q = 1) : d170997 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163603, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163603, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37444 q ha hb
  have h6 (q : Pattern) (ha : d163604 q = 1) (hb : d169395 q = 1) : d170998 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163604, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163604, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d163605 q = 1) (hb : d169395 q = 1) : d170999 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163605, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163605, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d163606 q = 1) (hb : d169395 q = 1) : d171000 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163606, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d163606, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d163607 q = 1) (hb : d169395 q = 1) : d171001 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163607, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163607, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163622 q = 1) (hb : d169395 q = 1) : d171016 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d163622, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163622, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37447 q ha hb
  have h11 (q : Pattern) (ha : d163623 q = 1) (hb : d169395 q = 1) : d171017 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d163623, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163623, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d163624 q = 1) (hb : d169395 q = 1) : d171018 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d163624, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d163624, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d163625 q = 1) (hb : d169395 q = 1) : d171019 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d163625, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d163625, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d163626 q = 1) (hb : d169395 q = 1) : d171020 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d163626, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d163626, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d163627 q = 1) (hb : d169395 q = 1) : d171021 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d163627, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d163627, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro37449 (p : Pattern) (ha : d163633 p = 1) (hb : d169395 p = 1) : d171027 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163628 q = 1) (hb : d169395 q = 1) : d171022 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d163628, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163628, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37448 q ha hb
  have h2 (q : Pattern) (ha : d163629 q = 1) (hb : d169395 q = 1) : d171023 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d163629, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163629, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d163630 q = 1) (hb : d169395 q = 1) : d171024 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d163630, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163630, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163631 q = 1) (hb : d169395 q = 1) : d171025 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d163631, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163631, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d163632 q = 1) (hb : d169395 q = 1) : d171026 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d163632, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163632, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163633 q = 1) (hb : d169395 q = 1) : d171027 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d163633, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163633, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37450 (p : Pattern) (ha : d163639 p = 1) (hb : d169395 p = 1) : d171033 p = 1 := by
  have h0 (q : Pattern) (ha : d163496 q = 1) (hb : d169395 q = 1) : d170890 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163496, d170890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37423 q ha hb
    | true =>
      simp only [d163496, d170890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37427 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d163523 q = 1) (hb : d169395 q = 1) : d170917 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163523, d170917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163523, d170917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37431 q ha hb
  have h3 (q : Pattern) (ha : d163524 q = 1) (hb : d169395 q = 1) : d170918 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163524, d170918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d163524, d170918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d163559 q = 1) (hb : d169395 q = 1) : d170953 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163559, d170953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163559, d170953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37437 q ha hb
  have h5 (q : Pattern) (ha : d163560 q = 1) (hb : d169395 q = 1) : d170954 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163560, d170954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163560, d170954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d163561 q = 1) (hb : d169395 q = 1) : d170955 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163561, d170955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163561, d170955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d163596 q = 1) (hb : d169395 q = 1) : d170990 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163596, d170990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163596, d170990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37443 q ha hb
  have h8 (q : Pattern) (ha : d163597 q = 1) (hb : d169395 q = 1) : d170991 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163597, d170991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163597, d170991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d163598 q = 1) (hb : d169395 q = 1) : d170992 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163598, d170992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163598, d170992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d163599 q = 1) (hb : d169395 q = 1) : d170993 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163599, d170993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d163599, d170993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d163634 q = 1) (hb : d169395 q = 1) : d171028 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d163634, d171028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163634, d171028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37449 q ha hb
  have h12 (q : Pattern) (ha : d163635 q = 1) (hb : d169395 q = 1) : d171029 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d163635, d171029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163635, d171029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d163636 q = 1) (hb : d169395 q = 1) : d171030 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d163636, d171030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163636, d171030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d163637 q = 1) (hb : d169395 q = 1) : d171031 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d163637, d171031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163637, d171031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d163638 q = 1) (hb : d169395 q = 1) : d171032 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d163638, d171032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d163638, d171032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d163639 q = 1) (hb : d169395 q = 1) : d171033 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d163639, d171033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d163639, d171033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro37451 (p : Pattern) (ha : d163645 p = 1) (hb : d169395 p = 1) : d171039 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163640 q = 1) (hb : d169395 q = 1) : d171034 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d163640, d171034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37450 q ha hb
    | true =>
      simp only [d163640, d171034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163641 q = 1) (hb : d169395 q = 1) : d171035 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d163641, d171035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163641, d171035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163642 q = 1) (hb : d169395 q = 1) : d171036 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d163642, d171036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163642, d171036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163643 q = 1) (hb : d169395 q = 1) : d171037 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d163643, d171037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163643, d171037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163644 q = 1) (hb : d169395 q = 1) : d171038 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d163644, d171038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163644, d171038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163645 q = 1) (hb : d169395 q = 1) : d171039 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d163645, d171039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163645, d171039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37452 (p : Pattern) (ha : d163651 p = 1) (hb : d169395 p = 1) : d171045 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163646 q = 1) (hb : d169395 q = 1) : d171040 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d163646, d171040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37451 q ha hb
    | true =>
      simp only [d163646, d171040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163647 q = 1) (hb : d169395 q = 1) : d171041 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d163647, d171041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163647, d171041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163648 q = 1) (hb : d169395 q = 1) : d171042 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d163648, d171042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163648, d171042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163649 q = 1) (hb : d169395 q = 1) : d171043 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d163649, d171043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163649, d171043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163650 q = 1) (hb : d169395 q = 1) : d171044 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d163650, d171044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163650, d171044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163651 q = 1) (hb : d169395 q = 1) : d171045 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d163651, d171045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163651, d171045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37453 (p : Pattern) (ha : d163657 p = 1) (hb : d169397 p = 1) : d171051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169395 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163652 q = 1) (hb : d169395 q = 1) : d171046 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d163652, d171046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37452 q ha hb
    | true =>
      simp only [d163652, d171046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163653 q = 1) (hb : d169395 q = 1) : d171047 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d163653, d171047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163653, d171047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163654 q = 1) (hb : d169395 q = 1) : d171048 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d163654, d171048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163654, d171048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163655 q = 1) (hb : d169395 q = 1) : d171049 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d163655, d171049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163655, d171049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163656 q = 1) (hb : d169395 q = 1) : d171050 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d163656, d171050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163656, d171050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d169396 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d163657 q = 1) (hb : d169397 q = 1) : d171051 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d163657, d169397, d171051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163657, d169397, d171051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro37454 (p : Pattern) (ha : d163663 p = 1) (hb : d169397 p = 1) : d171057 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163658 q = 1) (hb : d169397 q = 1) : d171052 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d163658, d171052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37453 q ha hb
    | true =>
      simp only [d163658, d171052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163659 q = 1) (hb : d169397 q = 1) : d171053 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d163659, d171053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163659, d171053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163660 q = 1) (hb : d169397 q = 1) : d171054 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d163660, d171054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163660, d171054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163661 q = 1) (hb : d169397 q = 1) : d171055 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d163661, d171055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163661, d171055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163662 q = 1) (hb : d169397 q = 1) : d171056 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d163662, d171056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163662, d171056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163663 q = 1) (hb : d169397 q = 1) : d171057 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d163663, d171057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163663, d171057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37455 (p : Pattern) (ha : d163669 p = 1) (hb : d169397 p = 1) : d171063 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163664 q = 1) (hb : d169397 q = 1) : d171058 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d163664, d171058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37454 q ha hb
    | true =>
      simp only [d163664, d171058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163665 q = 1) (hb : d169397 q = 1) : d171059 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d163665, d171059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163665, d171059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163666 q = 1) (hb : d169397 q = 1) : d171060 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d163666, d171060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163666, d171060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163667 q = 1) (hb : d169397 q = 1) : d171061 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d163667, d171061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163667, d171061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163668 q = 1) (hb : d169397 q = 1) : d171062 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d163668, d171062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163668, d171062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163669 q = 1) (hb : d169397 q = 1) : d171063 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d163669, d171063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163669, d171063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37456 (p : Pattern) (ha : d163675 p = 1) (hb : d169397 p = 1) : d171069 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163670 q = 1) (hb : d169397 q = 1) : d171064 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d163670, d171064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37455 q ha hb
    | true =>
      simp only [d163670, d171064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163671 q = 1) (hb : d169397 q = 1) : d171065 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d163671, d171065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163671, d171065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163672 q = 1) (hb : d169397 q = 1) : d171066 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d163672, d171066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163672, d171066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163673 q = 1) (hb : d169397 q = 1) : d171067 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d163673, d171067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163673, d171067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163674 q = 1) (hb : d169397 q = 1) : d171068 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d163674, d171068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163674, d171068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163675 q = 1) (hb : d169397 q = 1) : d171069 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d163675, d171069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163675, d171069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37457 (p : Pattern) (ha : d163681 p = 1) (hb : d169397 p = 1) : d171075 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d169397 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d163676 q = 1) (hb : d169397 q = 1) : d171070 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d163676, d171070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37456 q ha hb
    | true =>
      simp only [d163676, d171070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d163677 q = 1) (hb : d169397 q = 1) : d171071 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d163677, d171071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d163677, d171071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d163678 q = 1) (hb : d169397 q = 1) : d171072 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d163678, d171072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d163678, d171072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d163679 q = 1) (hb : d169397 q = 1) : d171073 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d163679, d171073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d163679, d171073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d163680 q = 1) (hb : d169397 q = 1) : d171074 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d163680, d171074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d163680, d171074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d163681 q = 1) (hb : d169397 q = 1) : d171075 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d163681, d171075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d163681, d171075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro37458 (p : Pattern) (ha : d146966 p = 1) (hb : d169470 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d146852 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
    | true =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h5 (q : Pattern) (ha : d146956 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d146956, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d146963 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d146963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d146964 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d146965 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d146966 q = 1) (hb : d169470 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146966, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146966, d169470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37459 (p : Pattern) (ha : d146985 p = 1) (hb : d169477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146928 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146934 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146955 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146852 q = 1) (hb : d169411 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37124 q ha hb
    | true =>
      simp only [d146852, d169411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro5 q hb ha
  have h4 (q : Pattern) (ha : d146956 q = 1) (hb : d169466 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146956, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d146956, d169466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d146962 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d146963 q = 1) (hb : d169467 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d146963, d169467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d146964 q = 1) (hb : d169468 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146964, d169468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146965 q = 1) (hb : d169469 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146965, d169469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d146971 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d146975 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d146859 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37126 q ha hb
    | true =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h13 (q : Pattern) (ha : d146978 q = 1) (hb : d169473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d146978, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d146982 q = 1) (hb : d169474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d146982, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d146983 q = 1) (hb : d169475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146983, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d146983, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d146984 q = 1) (hb : d169476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146984, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d146984, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d146985 q = 1) (hb : d169477 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146985, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d146985, d169477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro37460 (p : Pattern) (ha : d146994 p = 1) (hb : d170841 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d146977 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146859 q = 1) (hb : d169418 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37126 q ha hb
    | true =>
      simp only [d146859, d169418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro7 q hb ha
  have h3 (q : Pattern) (ha : d146978 q = 1) (hb : d169473 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d146978, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d146978, d169473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d146981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146982 q = 1) (hb : d169474 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d146982, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146982, d169474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146992 q = 1) (hb : d169475 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d146992, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146992, d169475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146993 q = 1) (hb : d169476 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d146993, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146993, d169476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d146994 q = 1) (hb : d170841 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d146994, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146994, d170841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37461 (p : Pattern) (ha : d147030 p = 1) (hb : d170851 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147019 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d146891 q = 1) (hb : d169449 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d146891, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37131 q ha hb
    | true =>
      simp only [d146891, d169449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro12 q hb ha
  have h3 (q : Pattern) (ha : d147020 q = 1) (hb : d170847 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147020, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147020, d170847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147027 q = 1) (hb : d170848 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147027, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147027, d170848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147028 q = 1) (hb : d170849 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147028, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147028, d170849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147029 q = 1) (hb : d170850 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147029, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147029, d170850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147030 q = 1) (hb : d170851 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147030, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147030, d170851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37462 (p : Pattern) (ha : d147036 p = 1) (hb : d170857 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d146922 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d146986 q = 1) (hb : d169478 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146986, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37458 q ha hb
    | true =>
      simp only [d146986, d169478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37459 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d146988 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d146989 q = 1) (hb : d169479 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146989, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d146989, d169479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d146990 q = 1) (hb : d170839 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146990, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d146990, d170839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d146991 q = 1) (hb : d170840 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146991, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d146991, d170840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d146995 q = 1) (hb : d170842 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d146995, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d146995, d170842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37460 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52173 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d146996 q = 1) (hb : d170843 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d146996, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d146996, d170843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d146997 q = 1) (hb : d170844 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d146997, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d146997, d170844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d146998 q = 1) (hb : d170845 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d146998, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d146998, d170845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d146999 q = 1) (hb : d170846 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d146999, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d146999, d170846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147031 q = 1) (hb : d170852 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147031, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147031, d170852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37461 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d52210 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147032 q = 1) (hb : d170853 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147032, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147032, d170853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147033 q = 1) (hb : d170854 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147033, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147033, d170854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147034 q = 1) (hb : d170855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147034, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147034, d170855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147035 q = 1) (hb : d170856 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147035, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147035, d170856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147036 q = 1) (hb : d170857 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147036, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147036, d170857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro37463 (p : Pattern) (ha : d147042 p = 1) (hb : d170863 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d51951 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d53648 q = 1) (hb : d146903 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53648, d146903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro28391 q ha hb
  have h3 (q : Pattern) (ha : d53649 q = 1) (hb : d146904 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53649, d146904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53650 q = 1) (hb : d146905 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53650, d146905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53651 q = 1) (hb : d146906 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d53651, d146906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d53652 q = 1) (hb : d146907 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, d146907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147037 q = 1) (hb : d170858 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147037, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147037, d170858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37462 q ha hb
  have h8 (q : Pattern) (ha : d147038 q = 1) (hb : d170859 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147038, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147038, d170859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147039 q = 1) (hb : d170860 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147039, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147039, d170860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147040 q = 1) (hb : d170861 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147040, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147040, d170861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147041 q = 1) (hb : d170862 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147041, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147041, d170862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d147042 q = 1) (hb : d170863 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147042, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d147042, d170863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  exact h12 p ha hb
theorem andIntro37464 (p : Pattern) (ha : d147136 p = 1) (hb : d169612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147060 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37159 q ha hb
    | true =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37160 q ha hb
  have h5 (q : Pattern) (ha : d147126 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147126, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147133 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147133, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147134 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147134, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147135 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147135, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147136 q = 1) (hb : d169612 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147136, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147136, d169612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37465 (p : Pattern) (ha : d147157 p = 1) (hb : d169622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147086 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147095 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147125 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147060 q = 1) (hb : d169607 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37159 q ha hb
    | true =>
      simp only [d147060, d169607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37160 q ha hb
  have h4 (q : Pattern) (ha : d147126 q = 1) (hb : d169608 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147126, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147126, d169608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147132 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147133 q = 1) (hb : d169609 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147133, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147133, d169609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147134 q = 1) (hb : d169610 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147134, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147134, d169610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147135 q = 1) (hb : d169611 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147135, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147135, d169611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147142 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147147 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147070 q = 1) (hb : d169617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37162 q ha hb
    | true =>
      simp only [d147070, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37163 q ha hb
  have h13 (q : Pattern) (ha : d147150 q = 1) (hb : d169618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147150, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147154 q = 1) (hb : d169619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147154, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147155 q = 1) (hb : d169620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147155, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147155, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147156 q = 1) (hb : d169621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147156, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147156, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147157 q = 1) (hb : d169622 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147157, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147157, d169622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro37466 (p : Pattern) (ha : d147177 p = 1) (hb : d170866 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147149 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147070 q = 1) (hb : d169617 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147070, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37162 q ha hb
    | true =>
      simp only [d147070, d169617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37163 q ha hb
  have h3 (q : Pattern) (ha : d147150 q = 1) (hb : d169618 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147150, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147150, d169618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147153 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147154 q = 1) (hb : d169619 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147154, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147154, d169619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147175 q = 1) (hb : d169620 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147175, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147175, d169620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147176 q = 1) (hb : d169621 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147176, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147176, d169621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147177 q = 1) (hb : d170866 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147177, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147177, d170866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37467 (p : Pattern) (ha : d147241 p = 1) (hb : d170877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147225 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147230 q = 1) (hb : d170872 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147230, d170872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37192 q ha hb
    | true =>
      simp only [d147230, d170872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37195 q ha hb
  have h3 (q : Pattern) (ha : d147231 q = 1) (hb : d170873 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147231, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147231, d170873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147237 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147238 q = 1) (hb : d170874 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147238, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147238, d170874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147239 q = 1) (hb : d170875 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147239, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147239, d170875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147240 q = 1) (hb : d170876 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147240, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147240, d170876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147241 q = 1) (hb : d170877 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147241, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147241, d170877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37468 (p : Pattern) (ha : d147254 p = 1) (hb : d170883 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147078 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147158 q = 1) (hb : d169623 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147158, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37464 q ha hb
    | true =>
      simp only [d147158, d169623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37465 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147171 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147172 q = 1) (hb : d169624 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147172, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147172, d169624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147173 q = 1) (hb : d170864 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147173, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147173, d170864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147174 q = 1) (hb : d170865 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147174, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147174, d170865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147178 q = 1) (hb : d170867 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147178, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147178, d170867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37466 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147180 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147181 q = 1) (hb : d170868 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147181, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147181, d170868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147182 q = 1) (hb : d170869 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147182, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147182, d170869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147183 q = 1) (hb : d170870 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147183, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147183, d170870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147184 q = 1) (hb : d170871 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147184, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147184, d170871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147242 q = 1) (hb : d170878 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147242, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147242, d170878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37467 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147249 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147250 q = 1) (hb : d170879 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147250, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147250, d170879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147251 q = 1) (hb : d170880 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147251, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147251, d170880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147252 q = 1) (hb : d170881 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147252, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147252, d170881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147253 q = 1) (hb : d170882 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147253, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147253, d170882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147254 q = 1) (hb : d170883 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147254, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147254, d170883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro37469 (p : Pattern) (ha : d147260 p = 1) (hb : d170889 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147255 q = 1) (hb : d170884 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147255, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147255, d170884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37468 q ha hb
  have h2 (q : Pattern) (ha : d147256 q = 1) (hb : d170885 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147256, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147256, d170885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147257 q = 1) (hb : d170886 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147257, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147257, d170886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147258 q = 1) (hb : d170887 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147258, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147258, d170887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147259 q = 1) (hb : d170888 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147259, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147259, d170888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147260 q = 1) (hb : d170889 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147260, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147260, d170889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37470 (p : Pattern) (ha : d147365 p = 1) (hb : d169820 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147289 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37203 q ha hb
    | true =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37204 q ha hb
  have h5 (q : Pattern) (ha : d147355 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147355, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147362 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147362, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147363 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147363, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147364 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147364, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147365 q = 1) (hb : d169820 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147365, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147365, d169820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37471 (p : Pattern) (ha : d147386 p = 1) (hb : d169830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147315 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147324 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147354 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147289 q = 1) (hb : d169815 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37203 q ha hb
    | true =>
      simp only [d147289, d169815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37204 q ha hb
  have h4 (q : Pattern) (ha : d147355 q = 1) (hb : d169816 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147355, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147355, d169816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147361 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147362 q = 1) (hb : d169817 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147362, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147362, d169817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147363 q = 1) (hb : d169818 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147363, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147363, d169818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147364 q = 1) (hb : d169819 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147364, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147364, d169819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147371 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147376 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147299 q = 1) (hb : d169825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37206 q ha hb
    | true =>
      simp only [d147299, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37207 q ha hb
  have h13 (q : Pattern) (ha : d147379 q = 1) (hb : d169826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147379, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147383 q = 1) (hb : d169827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147383, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147384 q = 1) (hb : d169828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147384, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147384, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147385 q = 1) (hb : d169829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147385, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147385, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147386 q = 1) (hb : d169830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147386, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147386, d169830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro37472 (p : Pattern) (ha : d147406 p = 1) (hb : d170893 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147378 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147299 q = 1) (hb : d169825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147299, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37206 q ha hb
    | true =>
      simp only [d147299, d169825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37207 q ha hb
  have h3 (q : Pattern) (ha : d147379 q = 1) (hb : d169826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147379, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147379, d169826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147382 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147383 q = 1) (hb : d169827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147383, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147383, d169827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147404 q = 1) (hb : d169828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147404, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147404, d169828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147405 q = 1) (hb : d169829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147405, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147405, d169829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147406 q = 1) (hb : d170893 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147406, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147406, d170893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37473 (p : Pattern) (ha : d147480 p = 1) (hb : d170904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147464 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147469 q = 1) (hb : d170899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147469, d170899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37239 q ha hb
    | true =>
      simp only [d147469, d170899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37242 q ha hb
  have h3 (q : Pattern) (ha : d147470 q = 1) (hb : d170900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147470, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147470, d170900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147476 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147477 q = 1) (hb : d170901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147477, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147477, d170901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147478 q = 1) (hb : d170902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147478, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147478, d170902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147479 q = 1) (hb : d170903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147479, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147479, d170903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147480 q = 1) (hb : d170904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147480, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147480, d170904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37474 (p : Pattern) (ha : d147493 p = 1) (hb : d170910 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147307 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147387 q = 1) (hb : d169831 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147387, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37470 q ha hb
    | true =>
      simp only [d147387, d169831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37471 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147400 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147401 q = 1) (hb : d169832 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147401, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147401, d169832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147402 q = 1) (hb : d170891 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147402, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147402, d170891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147403 q = 1) (hb : d170892 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147403, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147403, d170892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147407 q = 1) (hb : d170894 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147407, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147407, d170894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37472 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147409 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147410 q = 1) (hb : d170895 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147410, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147410, d170895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147411 q = 1) (hb : d170896 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147411, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147411, d170896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147412 q = 1) (hb : d170897 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147412, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147412, d170897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147413 q = 1) (hb : d170898 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147413, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147413, d170898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147481 q = 1) (hb : d170905 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147481, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147481, d170905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37473 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147488 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147489 q = 1) (hb : d170906 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147489, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147489, d170906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147490 q = 1) (hb : d170907 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147490, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147490, d170907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147491 q = 1) (hb : d170908 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147491, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147491, d170908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147492 q = 1) (hb : d170909 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147492, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147492, d170909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147493 q = 1) (hb : d170910 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147493, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147493, d170910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro37475 (p : Pattern) (ha : d147499 p = 1) (hb : d170916 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147494 q = 1) (hb : d170911 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147494, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147494, d170911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37474 q ha hb
  have h2 (q : Pattern) (ha : d147495 q = 1) (hb : d170912 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147495, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147495, d170912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147496 q = 1) (hb : d170913 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147496, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147496, d170913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147497 q = 1) (hb : d170914 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147497, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147497, d170914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147498 q = 1) (hb : d170915 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147498, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147498, d170915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147499 q = 1) (hb : d170916 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147499, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147499, d170916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37476 (p : Pattern) (ha : d147664 p = 1) (hb : d170044 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147564 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37253 q ha hb
    | true =>
      simp only [d147564, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37254 q ha hb
  have h5 (q : Pattern) (ha : d147645 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147645, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d147661 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147661, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d147662 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147662, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d147663 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147663, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147664 q = 1) (hb : d170044 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147664, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147664, d170044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37477 (p : Pattern) (ha : d147686 p = 1) (hb : d170054 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147590 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147599 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147644 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147564 q = 1) (hb : d170039 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147564, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37253 q ha hb
    | true =>
      simp only [d147564, d170039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37254 q ha hb
  have h4 (q : Pattern) (ha : d147645 q = 1) (hb : d170040 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147645, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147645, d170040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d147660 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d147661 q = 1) (hb : d170041 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147661, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d147661, d170041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d147662 q = 1) (hb : d170042 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147662, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147662, d170042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147663 q = 1) (hb : d170043 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147663, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147663, d170043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d147670 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d147675 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147574 q = 1) (hb : d170049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37256 q ha hb
    | true =>
      simp only [d147574, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37257 q ha hb
  have h13 (q : Pattern) (ha : d147679 q = 1) (hb : d170050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d147679, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147683 q = 1) (hb : d170051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147683, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147684 q = 1) (hb : d170052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147684, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d147684, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d147685 q = 1) (hb : d170053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147685, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d147685, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d147686 q = 1) (hb : d170054 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147686, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d147686, d170054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro37478 (p : Pattern) (ha : d147711 p = 1) (hb : d170921 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147678 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147574 q = 1) (hb : d170049 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147574, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37256 q ha hb
    | true =>
      simp only [d147574, d170049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37257 q ha hb
  have h3 (q : Pattern) (ha : d147679 q = 1) (hb : d170050 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147679, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147679, d170050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147682 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147683 q = 1) (hb : d170051 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147683, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147683, d170051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147709 q = 1) (hb : d170052 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147709, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147709, d170052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147710 q = 1) (hb : d170053 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147710, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147710, d170053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147711 q = 1) (hb : d170921 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147711, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147711, d170921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37479 (p : Pattern) (ha : d147807 p = 1) (hb : d170928 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147765 q = 1) (hb : d170195 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147765, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37287 q ha hb
    | true =>
      simp only [d147765, d170195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
  have h2 (q : Pattern) (ha : d147766 q = 1) (hb : d170196 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147766, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147766, d170196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147767 q = 1) (hb : d170197 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147767, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147767, d170197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147774 q = 1) (hb : d170198 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147774, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
    | true =>
      simp only [d147774, d170198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37285 q hb ha
  have h5 (q : Pattern) (ha : d147775 q = 1) (hb : d170199 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147775, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147775, d170199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147776 q = 1) (hb : d170200 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147776, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147776, d170200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147777 q = 1) (hb : d170201 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147777, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147777, d170201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147793 q = 1) (hb : d170215 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d147793, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37289 q ha hb
    | true =>
      simp only [d147793, d170215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37293 q hb ha
  have h9 (q : Pattern) (ha : d147794 q = 1) (hb : d170216 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d147794, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147794, d170216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d147795 q = 1) (hb : d170217 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d147795, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147795, d170217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d147796 q = 1) (hb : d170218 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d147796, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147796, d170218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d147806 q = 1) (hb : d170927 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d147806, d170927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147806, d170927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147807 q = 1) (hb : d170928 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d147807, d170928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147807, d170928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37480 (p : Pattern) (ha : d147813 p = 1) (hb : d170934 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147808 q = 1) (hb : d170929 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147808, d170929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37479 q ha hb
    | true =>
      simp only [d147808, d170929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d147809 q = 1) (hb : d170930 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147809, d170930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147809, d170930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147799 q = 1) (hb : d170221 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d147799, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37294 q ha hb
    | true =>
      simp only [d147799, d170221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d147800 q = 1) (hb : d170222 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d147800, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147800, d170222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147810 q = 1) (hb : d170931 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d147810, d170931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d147810, d170931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147811 q = 1) (hb : d170932 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d147811, d170932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d147811, d170932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d147812 q = 1) (hb : d170933 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d147812, d170933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147812, d170933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d147813 q = 1) (hb : d170934 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d147813, d170934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147813, d170934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37481 (p : Pattern) (ha : d147838 p = 1) (hb : d170940 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147805 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147818 q = 1) (hb : d170935 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147818, d170935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37480 q ha hb
    | true =>
      simp only [d147818, d170935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37299 q ha hb
  have h3 (q : Pattern) (ha : d147819 q = 1) (hb : d170936 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147819, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d147819, d170936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d147834 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147835 q = 1) (hb : d170937 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d147835, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147835, d170937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147836 q = 1) (hb : d170938 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d147836, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147836, d170938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147837 q = 1) (hb : d170939 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d147837, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147837, d170939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d147838 q = 1) (hb : d170940 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d147838, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147838, d170940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37482 (p : Pattern) (ha : d147851 p = 1) (hb : d170946 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147582 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147687 q = 1) (hb : d170055 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147687, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37476 q ha hb
    | true =>
      simp only [d147687, d170055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37477 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147705 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147706 q = 1) (hb : d170056 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147706, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d147706, d170056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d147707 q = 1) (hb : d170919 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147707, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d147707, d170919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d147708 q = 1) (hb : d170920 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147708, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147708, d170920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d147712 q = 1) (hb : d170922 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147712, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147712, d170922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37478 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d147714 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d147715 q = 1) (hb : d170923 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147715, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d147715, d170923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d147716 q = 1) (hb : d170924 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147716, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d147716, d170924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d147717 q = 1) (hb : d170925 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147717, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d147717, d170925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d147718 q = 1) (hb : d170926 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147718, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d147718, d170926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d147839 q = 1) (hb : d170941 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d147839, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d147839, d170941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37481 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d147846 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d147847 q = 1) (hb : d170942 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d147847, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d147847, d170942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d147848 q = 1) (hb : d170943 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d147848, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d147848, d170943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d147849 q = 1) (hb : d170944 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d147849, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d147849, d170944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d147850 q = 1) (hb : d170945 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d147850, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d147850, d170945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d147851 q = 1) (hb : d170946 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d147851, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d147851, d170946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro37483 (p : Pattern) (ha : d147857 p = 1) (hb : d170952 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d147852 q = 1) (hb : d170947 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d147852, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147852, d170947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37482 q ha hb
  have h2 (q : Pattern) (ha : d147853 q = 1) (hb : d170948 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d147853, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147853, d170948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d147854 q = 1) (hb : d170949 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d147854, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147854, d170949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d147855 q = 1) (hb : d170950 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d147855, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147855, d170950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d147856 q = 1) (hb : d170951 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d147856, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147856, d170951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d147857 q = 1) (hb : d170952 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d147857, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d147857, d170952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37484 (p : Pattern) (ha : d148013 p = 1) (hb : d170310 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d147918 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37310 q ha hb
    | true =>
      simp only [d147918, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37311 q ha hb
  have h5 (q : Pattern) (ha : d147994 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d147994, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148010 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148010, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148011 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148011, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148012 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148012, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148013 q = 1) (hb : d170310 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148013, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148013, d170310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37485 (p : Pattern) (ha : d148035 p = 1) (hb : d170320 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147944 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d147953 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d147993 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d147918 q = 1) (hb : d170305 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147918, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37310 q ha hb
    | true =>
      simp only [d147918, d170305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37311 q ha hb
  have h4 (q : Pattern) (ha : d147994 q = 1) (hb : d170306 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d147994, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d147994, d170306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148009 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148010 q = 1) (hb : d170307 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148010, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148010, d170307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148011 q = 1) (hb : d170308 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148011, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148011, d170308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148012 q = 1) (hb : d170309 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148012, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148012, d170309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148019 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148024 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d147928 q = 1) (hb : d170315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37313 q ha hb
    | true =>
      simp only [d147928, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37314 q ha hb
  have h13 (q : Pattern) (ha : d148028 q = 1) (hb : d170316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148028, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148032 q = 1) (hb : d170317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148032, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148033 q = 1) (hb : d170318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148033, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148033, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148034 q = 1) (hb : d170319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148034, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148034, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148035 q = 1) (hb : d170320 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148035, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148035, d170320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro37486 (p : Pattern) (ha : d148060 p = 1) (hb : d170958 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148027 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d147928 q = 1) (hb : d170315 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d147928, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37313 q ha hb
    | true =>
      simp only [d147928, d170315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37314 q ha hb
  have h3 (q : Pattern) (ha : d148028 q = 1) (hb : d170316 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148028, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148028, d170316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148031 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148032 q = 1) (hb : d170317 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148032, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148032, d170317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148058 q = 1) (hb : d170318 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148058, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148058, d170318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148059 q = 1) (hb : d170319 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148059, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148059, d170319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148060 q = 1) (hb : d170958 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148060, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148060, d170958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37487 (p : Pattern) (ha : d148148 p = 1) (hb : d170965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148106 q = 1) (hb : d170459 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148106, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37343 q ha hb
    | true =>
      simp only [d148106, d170459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
  have h2 (q : Pattern) (ha : d148107 q = 1) (hb : d170460 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148107, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148107, d170460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148108 q = 1) (hb : d170461 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148108, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148108, d170461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148115 q = 1) (hb : d170462 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148115, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
    | true =>
      simp only [d148115, d170462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37341 q hb ha
  have h5 (q : Pattern) (ha : d148116 q = 1) (hb : d170463 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148116, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148116, d170463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148117 q = 1) (hb : d170464 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148117, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148117, d170464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148118 q = 1) (hb : d170465 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148118, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148118, d170465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148134 q = 1) (hb : d170479 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148134, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37345 q ha hb
    | true =>
      simp only [d148134, d170479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37349 q hb ha
  have h9 (q : Pattern) (ha : d148135 q = 1) (hb : d170480 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148135, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148135, d170480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148136 q = 1) (hb : d170481 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148136, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148136, d170481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148137 q = 1) (hb : d170482 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148137, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148137, d170482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148147 q = 1) (hb : d170964 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148147, d170964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148147, d170964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148148 q = 1) (hb : d170965 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148148, d170965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148148, d170965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37488 (p : Pattern) (ha : d148154 p = 1) (hb : d170971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148149 q = 1) (hb : d170966 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148149, d170966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37487 q ha hb
    | true =>
      simp only [d148149, d170966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148150 q = 1) (hb : d170967 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148150, d170967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148150, d170967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148140 q = 1) (hb : d170485 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148140, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37350 q ha hb
    | true =>
      simp only [d148140, d170485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148141 q = 1) (hb : d170486 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148141, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148141, d170486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148151 q = 1) (hb : d170968 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148151, d170968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148151, d170968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148152 q = 1) (hb : d170969 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148152, d170969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148152, d170969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148153 q = 1) (hb : d170970 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148153, d170970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148153, d170970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148154 q = 1) (hb : d170971 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148154, d170971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148154, d170971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37489 (p : Pattern) (ha : d148179 p = 1) (hb : d170977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148146 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148159 q = 1) (hb : d170972 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148159, d170972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37488 q ha hb
    | true =>
      simp only [d148159, d170972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37355 q ha hb
  have h3 (q : Pattern) (ha : d148160 q = 1) (hb : d170973 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148160, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148160, d170973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148175 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148176 q = 1) (hb : d170974 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148176, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148176, d170974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148177 q = 1) (hb : d170975 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148177, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148177, d170975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148178 q = 1) (hb : d170976 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148178, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148178, d170976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148179 q = 1) (hb : d170977 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148179, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148179, d170977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37490 (p : Pattern) (ha : d148192 p = 1) (hb : d170983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d147936 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148036 q = 1) (hb : d170321 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148036, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37484 q ha hb
    | true =>
      simp only [d148036, d170321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37485 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148054 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148055 q = 1) (hb : d170322 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148055, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148055, d170322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148056 q = 1) (hb : d170956 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148056, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148056, d170956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148057 q = 1) (hb : d170957 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148057, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148057, d170957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148061 q = 1) (hb : d170959 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148061, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148061, d170959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37486 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148063 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148064 q = 1) (hb : d170960 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148064, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148064, d170960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148065 q = 1) (hb : d170961 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148065, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148065, d170961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148066 q = 1) (hb : d170962 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148066, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148066, d170962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148067 q = 1) (hb : d170963 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148067, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148067, d170963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148180 q = 1) (hb : d170978 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148180, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148180, d170978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37489 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148187 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148188 q = 1) (hb : d170979 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148188, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148188, d170979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148189 q = 1) (hb : d170980 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148189, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148189, d170980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148190 q = 1) (hb : d170981 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148190, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148190, d170981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148191 q = 1) (hb : d170982 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148191, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148191, d170982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148192 q = 1) (hb : d170983 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148192, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148192, d170983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro37491 (p : Pattern) (ha : d148198 p = 1) (hb : d170989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148193 q = 1) (hb : d170984 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148193, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148193, d170984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37490 q ha hb
  have h2 (q : Pattern) (ha : d148194 q = 1) (hb : d170985 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148194, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148194, d170985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148195 q = 1) (hb : d170986 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148195, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148195, d170986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148196 q = 1) (hb : d170987 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148196, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148196, d170987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148197 q = 1) (hb : d170988 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148197, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148197, d170988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148198 q = 1) (hb : d170989 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148198, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148198, d170989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro37492 (p : Pattern) (ha : d148332 p = 1) (hb : d170574 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d148249 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37365 q ha hb
    | true =>
      simp only [d148249, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37366 q ha hb
  have h5 (q : Pattern) (ha : d148313 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d148313, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d148329 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148329, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d148330 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148330, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d148331 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148331, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148332 q = 1) (hb : d170574 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148332, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148332, d170574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro37493 (p : Pattern) (ha : d148354 p = 1) (hb : d170584 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148275 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148284 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148312 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148249 q = 1) (hb : d170569 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148249, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37365 q ha hb
    | true =>
      simp only [d148249, d170569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37366 q ha hb
  have h4 (q : Pattern) (ha : d148313 q = 1) (hb : d170570 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148313, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d148313, d170570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d148328 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d148329 q = 1) (hb : d170571 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148329, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d148329, d170571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d148330 q = 1) (hb : d170572 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148330, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148330, d170572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148331 q = 1) (hb : d170573 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148331, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148331, d170573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d148338 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d148343 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d148259 q = 1) (hb : d170579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37368 q ha hb
    | true =>
      simp only [d148259, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37369 q ha hb
  have h13 (q : Pattern) (ha : d148347 q = 1) (hb : d170580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d148347, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148351 q = 1) (hb : d170581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148351, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148352 q = 1) (hb : d170582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148352, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d148352, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d148353 q = 1) (hb : d170583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148353, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d148353, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d148354 q = 1) (hb : d170584 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148354, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d148354, d170584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro37494 (p : Pattern) (ha : d148379 p = 1) (hb : d170996 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148346 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148259 q = 1) (hb : d170579 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148259, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37368 q ha hb
    | true =>
      simp only [d148259, d170579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37369 q ha hb
  have h3 (q : Pattern) (ha : d148347 q = 1) (hb : d170580 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148347, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148347, d170580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148350 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148351 q = 1) (hb : d170581 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148351, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148351, d170581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148377 q = 1) (hb : d170582 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148377, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148377, d170582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148378 q = 1) (hb : d170583 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148378, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148378, d170583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148379 q = 1) (hb : d170996 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148379, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148379, d170996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37495 (p : Pattern) (ha : d148448 p = 1) (hb : d171003 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148406 q = 1) (hb : d170716 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148406, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37396 q ha hb
    | true =>
      simp only [d148406, d170716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
  have h2 (q : Pattern) (ha : d148407 q = 1) (hb : d170717 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148407, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148407, d170717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148408 q = 1) (hb : d170718 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148408, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148408, d170718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148415 q = 1) (hb : d170719 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148415, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
    | true =>
      simp only [d148415, d170719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37395 q hb ha
  have h5 (q : Pattern) (ha : d148416 q = 1) (hb : d170720 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148416, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148416, d170720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148417 q = 1) (hb : d170721 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148417, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148417, d170721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148418 q = 1) (hb : d170722 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148418, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148418, d170722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148434 q = 1) (hb : d170736 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d148434, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37398 q ha hb
    | true =>
      simp only [d148434, d170736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37402 q hb ha
  have h9 (q : Pattern) (ha : d148435 q = 1) (hb : d170737 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d148435, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148435, d170737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d148436 q = 1) (hb : d170738 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d148436, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148436, d170738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d148437 q = 1) (hb : d170739 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d148437, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148437, d170739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d148447 q = 1) (hb : d171002 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d148447, d171002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148447, d171002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148448 q = 1) (hb : d171003 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d148448, d171003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148448, d171003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro37496 (p : Pattern) (ha : d148454 p = 1) (hb : d171009 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148449 q = 1) (hb : d171004 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148449, d171004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37495 q ha hb
    | true =>
      simp only [d148449, d171004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d148450 q = 1) (hb : d171005 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148450, d171005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148450, d171005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148440 q = 1) (hb : d170742 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d148440, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37403 q ha hb
    | true =>
      simp only [d148440, d170742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d148441 q = 1) (hb : d170743 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d148441, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148441, d170743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148451 q = 1) (hb : d171006 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d148451, d171006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d148451, d171006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148452 q = 1) (hb : d171007 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d148452, d171007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d148452, d171007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d148453 q = 1) (hb : d171008 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d148453, d171008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148453, d171008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d148454 q = 1) (hb : d171009 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d148454, d171009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148454, d171009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro37497 (p : Pattern) (ha : d148479 p = 1) (hb : d171015 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d148446 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d148459 q = 1) (hb : d171010 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d148459, d171010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37496 q ha hb
    | true =>
      simp only [d148459, d171010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37408 q ha hb
  have h3 (q : Pattern) (ha : d148460 q = 1) (hb : d171011 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d148460, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d148460, d171011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d148475 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148476 q = 1) (hb : d171012 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d148476, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148476, d171012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148477 q = 1) (hb : d171013 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d148477, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148477, d171013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148478 q = 1) (hb : d171014 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d148478, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148478, d171014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d148479 q = 1) (hb : d171015 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d148479, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148479, d171015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro37498 (p : Pattern) (ha : d148492 p = 1) (hb : d171021 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d148267 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148355 q = 1) (hb : d170585 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148355, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37492 q ha hb
    | true =>
      simp only [d148355, d170585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37493 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d148373 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d148374 q = 1) (hb : d170586 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148374, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d148374, d170586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d148375 q = 1) (hb : d170994 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148375, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d148375, d170994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d148376 q = 1) (hb : d170995 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148376, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148376, d170995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d148380 q = 1) (hb : d170997 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148380, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148380, d170997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37494 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d148382 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d148383 q = 1) (hb : d170998 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148383, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d148383, d170998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d148384 q = 1) (hb : d170999 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148384, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d148384, d170999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d148385 q = 1) (hb : d171000 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148385, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d148385, d171000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d148386 q = 1) (hb : d171001 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148386, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d148386, d171001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d148480 q = 1) (hb : d171016 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d148480, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d148480, d171016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37497 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d148487 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d148488 q = 1) (hb : d171017 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d148488, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d148488, d171017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d148489 q = 1) (hb : d171018 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d148489, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d148489, d171018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d148490 q = 1) (hb : d171019 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d148490, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d148490, d171019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d148491 q = 1) (hb : d171020 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d148491, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d148491, d171020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d148492 q = 1) (hb : d171021 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d148492, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d148492, d171021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro37499 (p : Pattern) (ha : d148498 p = 1) (hb : d171027 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d148493 q = 1) (hb : d171022 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d148493, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148493, d171022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro37498 q ha hb
  have h2 (q : Pattern) (ha : d148494 q = 1) (hb : d171023 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d148494, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148494, d171023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d148495 q = 1) (hb : d171024 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d148495, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148495, d171024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d148496 q = 1) (hb : d171025 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d148496, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148496, d171025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d148497 q = 1) (hb : d171026 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d148497, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148497, d171026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d148498 q = 1) (hb : d171027 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d148498, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d148498, d171027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
end NetHack.Soko22Hazard87
