import NetHack.Soko22Hazard87.AndIntroBlocks0121
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.PatternCorrection
theorem andIntro30500 (p : Pattern) (ha : d155542 p = 1) (hb : d157124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155542 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d51983 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d52685 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d52685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1116 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1116, d52686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1132 q = 1) (hb : d52686 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9841 q = 1) (hb : d155541 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, d155541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9841, d155541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9842 q = 1) (hb : d155542 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, d155542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9842, d155542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d155542 q = 1) (hb : d157124 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro30501 (p : Pattern) (ha : d155549 p = 1) (hb : d157130 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155535 q = 1) (hb : d157118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155535, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30498 q ha hb
    | true =>
      simp only [d155535, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155536 q = 1) (hb : d157119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155536, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155536, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155537 q = 1) (hb : d157120 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155537, d157120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155537, d157120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155538 q = 1) (hb : d157121 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155538, d157121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155538, d157121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155543 q = 1) (hb : d157125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155543, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30500 q ha hb
    | true =>
      simp only [d155543, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155544 q = 1) (hb : d157126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155544, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155544, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155545 q = 1) (hb : d157127 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155545, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155545, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155546 q = 1) (hb : d157128 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155546, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155546, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155547 q = 1) (hb : d157129 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155547, d157129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155547, d157129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155548 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d155549 q = 1) (hb : d157130 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155549, d157130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155549, d157130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro30502 (p : Pattern) (ha : d155554 p = 1) (hb : d157124 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155554 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69101 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1115 q = 1) (hb : d69102 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d69102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1115, d69102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1116 q = 1) (hb : d69103 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1116, d69103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1116, d69103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69103 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d1132 q = 1) (hb : d69103 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d1132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d19 q = 1) (hb : d51871 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
    | true =>
      simp only [d19, d51871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d20 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d20, d51872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d21 q = 1) (hb : d51872 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d21, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d9841 q = 1) (hb : d155553 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d9841, d155553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d9841, d155553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d9842 q = 1) (hb : d155554 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d9842, d155554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d9842, d155554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d155554 q = 1) (hb : d157124 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro30503 (p : Pattern) (ha : d155560 p = 1) (hb : d157135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155555 q = 1) (hb : d157125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155555, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30502 q ha hb
    | true =>
      simp only [d155555, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155556 q = 1) (hb : d157126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155556, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155556, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155557 q = 1) (hb : d157127 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155557, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155557, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155558 q = 1) (hb : d157128 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155558, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155558, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155559 q = 1) (hb : d157134 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155559, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155559, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155560 q = 1) (hb : d157135 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155560, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155560, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30504 (p : Pattern) (ha : d155566 p = 1) (hb : d157135 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155543 q = 1) (hb : d157125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155543, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30500 q ha hb
    | true =>
      simp only [d155543, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155544 q = 1) (hb : d157126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155544, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155544, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155545 q = 1) (hb : d157127 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155545, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155545, d157127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155546 q = 1) (hb : d157128 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155546, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155546, d157128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155565 q = 1) (hb : d157134 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155565, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155565, d157134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155566 q = 1) (hb : d157135 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155566, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155566, d157135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30505 (p : Pattern) (ha : d155572 p = 1) (hb : d157142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155550 q = 1) (hb : d157131 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155550, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30499 q ha hb
    | true =>
      simp only [d155550, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30501 q ha hb
  have h2 (q : Pattern) (ha : d155551 q = 1) (hb : d157132 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155551, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155551, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155552 q = 1) (hb : d157133 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155552, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155552, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155561 q = 1) (hb : d157136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155561, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30501 q ha hb
    | true =>
      simp only [d155561, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30503 q ha hb
  have h5 (q : Pattern) (ha : d155562 q = 1) (hb : d157137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155562, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155562, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155563 q = 1) (hb : d157138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155563, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155563, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155564 q = 1) (hb : d157139 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155564, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155564, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155567 q = 1) (hb : d157136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155567, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30501 q ha hb
    | true =>
      simp only [d155567, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30504 q ha hb
  have h9 (q : Pattern) (ha : d155568 q = 1) (hb : d157137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155568, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155568, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155569 q = 1) (hb : d157138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155569, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155569, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155570 q = 1) (hb : d157140 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155570, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155570, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155571 q = 1) (hb : d157141 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155571, d157141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155571, d157141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155572 q = 1) (hb : d157142 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155572, d157142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155572, d157142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro30506 (p : Pattern) (ha : d155576 p = 1) (hb : d157146 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155567 q = 1) (hb : d157136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155567, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30501 q ha hb
    | true =>
      simp only [d155567, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30504 q ha hb
  have h2 (q : Pattern) (ha : d155568 q = 1) (hb : d157137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155568, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155568, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155569 q = 1) (hb : d157138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155569, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155569, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155570 q = 1) (hb : d157140 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155570, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155570, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155575 q = 1) (hb : d157145 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155575, d157145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155575, d157145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155576 q = 1) (hb : d157146 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155576, d157146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155576, d157146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30507 (p : Pattern) (ha : d155582 p = 1) (hb : d157152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155573 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30505 q ha hb
    | true =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155574 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155579 q = 1) (hb : d157149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155580 q = 1) (hb : d157150 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155580, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155580, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155581 q = 1) (hb : d157151 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155581, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155581, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155582 q = 1) (hb : d157152 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155582, d157152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155582, d157152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30508 (p : Pattern) (ha : d155586 p = 1) (hb : d157156 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155583 q = 1) (hb : d157153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155584 q = 1) (hb : d157154 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155584, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155584, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155585 q = 1) (hb : d157155 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155585, d157155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155585, d157155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155586 q = 1) (hb : d157156 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155586, d157156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155586, d157156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30509 (p : Pattern) (ha : d155592 p = 1) (hb : d157162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155587 q = 1) (hb : d157157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155587, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30507 q ha hb
    | true =>
      simp only [d155587, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30508 q ha hb
  have h2 (q : Pattern) (ha : d155588 q = 1) (hb : d157158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155588, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155588, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155589 q = 1) (hb : d157159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155589, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155589, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155590 q = 1) (hb : d157160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155590, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155590, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155591 q = 1) (hb : d157161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155591, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155591, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155592 q = 1) (hb : d157162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155592, d157162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155592, d157162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30510 (p : Pattern) (ha : d155595 p = 1) (hb : d157165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155573 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30505 q ha hb
    | true =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155574 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155579 q = 1) (hb : d157149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155580 q = 1) (hb : d157150 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155580, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155580, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155581 q = 1) (hb : d157151 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155581, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155581, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155595 q = 1) (hb : d157165 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155595, d157165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155595, d157165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30511 (p : Pattern) (ha : d155596 p = 1) (hb : d157166 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155583 q = 1) (hb : d157153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155584 q = 1) (hb : d157154 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155584, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155584, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155585 q = 1) (hb : d157155 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155585, d157155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155585, d157155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155596 q = 1) (hb : d157166 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155596, d157166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155596, d157166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30512 (p : Pattern) (ha : d155602 p = 1) (hb : d157172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155587 q = 1) (hb : d157157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155587, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30507 q ha hb
    | true =>
      simp only [d155587, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30508 q ha hb
  have h2 (q : Pattern) (ha : d155588 q = 1) (hb : d157158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155588, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155588, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155589 q = 1) (hb : d157159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155589, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155589, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155590 q = 1) (hb : d157160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155590, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155590, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155591 q = 1) (hb : d157161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155591, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155591, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155597 q = 1) (hb : d157167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155597, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30510 q ha hb
    | true =>
      simp only [d155597, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30511 q ha hb
  have h7 (q : Pattern) (ha : d155598 q = 1) (hb : d157168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155598, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155598, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155599 q = 1) (hb : d157169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155599, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155599, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155600 q = 1) (hb : d157170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155600, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155600, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155601 q = 1) (hb : d157171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155601, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155601, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155602 q = 1) (hb : d157172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155602, d157172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155602, d157172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30513 (p : Pattern) (ha : d155607 p = 1) (hb : d157177 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155573 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30505 q ha hb
    | true =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155574 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155579 q = 1) (hb : d157149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155580 q = 1) (hb : d157150 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155580, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155580, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155606 q = 1) (hb : d157176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155606, d157176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155606, d157176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155607 q = 1) (hb : d157177 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155607, d157177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155607, d157177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30514 (p : Pattern) (ha : d155609 p = 1) (hb : d157179 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155583 q = 1) (hb : d157153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155584 q = 1) (hb : d157154 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155584, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155584, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155608 q = 1) (hb : d157178 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155608, d157178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155608, d157178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155609 q = 1) (hb : d157179 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155609, d157179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155609, d157179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30515 (p : Pattern) (ha : d155616 p = 1) (hb : d157186 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155573 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30505 q ha hb
    | true =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155574 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155579 q = 1) (hb : d157149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155614 q = 1) (hb : d157184 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155614, d157184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155614, d157184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155615 q = 1) (hb : d157185 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155615, d157185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155615, d157185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155616 q = 1) (hb : d157186 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155616, d157186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155616, d157186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30516 (p : Pattern) (ha : d155619 p = 1) (hb : d157189 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155583 q = 1) (hb : d157153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155617 q = 1) (hb : d157187 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155617, d157187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155617, d157187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155618 q = 1) (hb : d157188 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155618, d157188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155618, d157188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155619 q = 1) (hb : d157189 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155619, d157189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155619, d157189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30517 (p : Pattern) (ha : d155624 p = 1) (hb : d157193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155624 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d822 q = 1) (hb : d52499 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro120 q ha hb
    | true =>
      simp only [d822, d52499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d823 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d823, d52500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d9759 q = 1) (hb : d52500 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d9759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d828 q = 1) (hb : d52505 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro121 q ha hb
    | true =>
      simp only [d828, d52505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d829 q = 1) (hb : d52506 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d829, d52506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52506 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d25761 q = 1) (hb : d52506 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d25761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d25762 q = 1) (hb : d155623 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d25762, d155623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d25762, d155623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d25763 q = 1) (hb : d155624 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d25763, d155624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d25763, d155624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d155624 q = 1) (hb : d157193 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro30518 (p : Pattern) (ha : d155631 p = 1) (hb : d157199 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155625 q = 1) (hb : d157194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155625, d157194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30517 q ha hb
    | true =>
      simp only [d155625, d157194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155626 q = 1) (hb : d157195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155626, d157195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155626, d157195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155627 q = 1) (hb : d157196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155627, d157196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155627, d157196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155628 q = 1) (hb : d157197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155628, d157197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155628, d157197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155529 q = 1) (hb : d157113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155529, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30497 q ha hb
    | true =>
      simp only [d155529, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155530 q = 1) (hb : d157114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155530, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155530, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155531 q = 1) (hb : d157115 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155531, d157115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155531, d157115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155532 q = 1) (hb : d157116 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155532, d157116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155532, d157116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155629 q = 1) (hb : d157198 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155629, d157198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155629, d157198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155630 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d155631 q = 1) (hb : d157199 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155631, d157199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155631, d157199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro30519 (p : Pattern) (ha : d155636 p = 1) (hb : d157206 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155636 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d9772 q = 1) (hb : d101293 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23289 q ha hb
    | true =>
      simp only [d9772, d101293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23312 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d9773 q = 1) (hb : d101294 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d9773, d101294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101294 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101294 q = 1) (hb : d157203 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d157203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d157203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155635 q = 1) (hb : d157204 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d155635, d157204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155635, d157204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h7 (q : Pattern) (ha : d155636 q = 1) (hb : d157205 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d155636, d157205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155636, d157205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h8 (q : Pattern) (ha : d155636 q = 1) (hb : d157206 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30520 (p : Pattern) (ha : d155642 p = 1) (hb : d157212 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155637 q = 1) (hb : d157207 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155637, d157207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30519 q ha hb
    | true =>
      simp only [d155637, d157207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155638 q = 1) (hb : d157208 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155638, d157208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155638, d157208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155639 q = 1) (hb : d157209 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155639, d157209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155639, d157209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155640 q = 1) (hb : d157210 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155640, d157210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155640, d157210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d155189 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d155641 q = 1) (hb : d157211 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155641, d157211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155641, d157211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d155548 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d155642 q = 1) (hb : d157212 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155642, d157212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155642, d157212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro30521 (p : Pattern) (ha : d155648 p = 1) (hb : d157218 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155632 q = 1) (hb : d157200 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155632, d157200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30518 q ha hb
    | true =>
      simp only [d155632, d157200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30499 q ha hb
  have h2 (q : Pattern) (ha : d155633 q = 1) (hb : d157201 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155633, d157201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155633, d157201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155634 q = 1) (hb : d157202 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155634, d157202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155634, d157202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155643 q = 1) (hb : d157213 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155643, d157213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30499 q ha hb
    | true =>
      simp only [d155643, d157213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30520 q ha hb
  have h5 (q : Pattern) (ha : d155644 q = 1) (hb : d157214 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155644, d157214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155644, d157214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155645 q = 1) (hb : d157215 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155645, d157215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155645, d157215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155646 q = 1) (hb : d157216 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155646, d157216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155646, d157216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155550 q = 1) (hb : d157131 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155550, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30499 q ha hb
    | true =>
      simp only [d155550, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30501 q ha hb
  have h9 (q : Pattern) (ha : d155551 q = 1) (hb : d157132 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155551, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155551, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155552 q = 1) (hb : d157133 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155552, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155552, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155561 q = 1) (hb : d157136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155561, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30501 q ha hb
    | true =>
      simp only [d155561, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30503 q ha hb
  have h12 (q : Pattern) (ha : d155562 q = 1) (hb : d157137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155562, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155562, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155563 q = 1) (hb : d157138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155563, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155563, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155564 q = 1) (hb : d157139 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155564, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155564, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155647 q = 1) (hb : d157217 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155647, d157217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155647, d157217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155648 q = 1) (hb : d157218 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155648, d157218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155648, d157218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro30522 (p : Pattern) (ha : d155653 p = 1) (hb : d157142 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155550 q = 1) (hb : d157131 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155550, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30499 q ha hb
    | true =>
      simp only [d155550, d157131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30501 q ha hb
  have h2 (q : Pattern) (ha : d155551 q = 1) (hb : d157132 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155551, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155551, d157132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155552 q = 1) (hb : d157133 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155552, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155552, d157133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155561 q = 1) (hb : d157136 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155561, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30501 q ha hb
    | true =>
      simp only [d155561, d157136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30503 q ha hb
  have h5 (q : Pattern) (ha : d155562 q = 1) (hb : d157137 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155562, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155562, d157137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155563 q = 1) (hb : d157138 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155563, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155563, d157138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155564 q = 1) (hb : d157139 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155564, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155564, d157139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155651 q = 1) (hb : d157140 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155651, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155651, d157140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155652 q = 1) (hb : d157141 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155652, d157141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155652, d157141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155653 q = 1) (hb : d157142 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155653, d157142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155653, d157142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30523 (p : Pattern) (ha : d155659 p = 1) (hb : d157224 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155649 q = 1) (hb : d157219 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155649, d157219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30521 q ha hb
    | true =>
      simp only [d155649, d157219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155650 q = 1) (hb : d157220 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155650, d157220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155650, d157220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155654 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155654, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30522 q ha hb
    | true =>
      simp only [d155654, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155655 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155655, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155655, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155656 q = 1) (hb : d157221 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155656, d157221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155656, d157221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155657 q = 1) (hb : d157222 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155657, d157222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155657, d157222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155658 q = 1) (hb : d157223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155658, d157223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155658, d157223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155659 q = 1) (hb : d157224 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155659, d157224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155659, d157224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30524 (p : Pattern) (ha : d155663 p = 1) (hb : d157152 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155654 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155654, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30522 q ha hb
    | true =>
      simp only [d155654, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155655 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155655, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155655, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155660 q = 1) (hb : d157149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155660, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155660, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155661 q = 1) (hb : d157150 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155661, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155661, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155662 q = 1) (hb : d157151 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155662, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155662, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155663 q = 1) (hb : d157152 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155663, d157152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155663, d157152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30525 (p : Pattern) (ha : d155669 p = 1) (hb : d157230 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155573 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30505 q ha hb
    | true =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155574 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155666 q = 1) (hb : d157227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155666, d157227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155666, d157227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155667 q = 1) (hb : d157228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155667, d157228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155667, d157228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155668 q = 1) (hb : d157229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155668, d157229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155668, d157229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155669 q = 1) (hb : d157230 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155669, d157230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155669, d157230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30526 (p : Pattern) (ha : d155675 p = 1) (hb : d157236 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155610 q = 1) (hb : d157180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155610, d157180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30513 q ha hb
    | true =>
      simp only [d155610, d157180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30514 q ha hb
  have h2 (q : Pattern) (ha : d155611 q = 1) (hb : d157181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155611, d157181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155611, d157181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155612 q = 1) (hb : d157182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155612, d157182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155612, d157182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155613 q = 1) (hb : d157183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155613, d157183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155613, d157183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155620 q = 1) (hb : d157190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155620, d157190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30515 q ha hb
    | true =>
      simp only [d155620, d157190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30516 q ha hb
  have h6 (q : Pattern) (ha : d155621 q = 1) (hb : d157191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155621, d157191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155621, d157191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155622 q = 1) (hb : d157192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155622, d157192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155622, d157192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155664 q = 1) (hb : d157225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155664, d157225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30523 q ha hb
    | true =>
      simp only [d155664, d157225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30524 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155587 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155665 q = 1) (hb : d157226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155665, d157226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155665, d157226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d155670 q = 1) (hb : d157231 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155670, d157231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30525 q ha hb
    | true =>
      simp only [d155670, d157231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155671 q = 1) (hb : d157232 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155671, d157232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155671, d157232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155672 q = 1) (hb : d157233 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155672, d157233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155672, d157233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155673 q = 1) (hb : d157234 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155673, d157234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155673, d157234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155674 q = 1) (hb : d157235 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155674, d157235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155674, d157235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155675 q = 1) (hb : d157236 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155675, d157236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155675, d157236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro30527 (p : Pattern) (ha : d155676 p = 1) (hb : d157237 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155573 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30505 q ha hb
    | true =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155574 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155579 q = 1) (hb : d157149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155580 q = 1) (hb : d157150 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155580, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155580, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155606 q = 1) (hb : d157176 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155606, d157176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155606, d157176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155676 q = 1) (hb : d157237 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155676, d157237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155676, d157237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30528 (p : Pattern) (ha : d155677 p = 1) (hb : d157238 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155583 q = 1) (hb : d157153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155584 q = 1) (hb : d157154 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155584, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155584, d157154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155608 q = 1) (hb : d157178 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155608, d157178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155608, d157178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155677 q = 1) (hb : d157238 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155677, d157238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155677, d157238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30529 (p : Pattern) (ha : d155682 p = 1) (hb : d157243 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155573 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30505 q ha hb
    | true =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155574 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155579 q = 1) (hb : d157149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155579, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155614 q = 1) (hb : d157184 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155614, d157184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155614, d157184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155615 q = 1) (hb : d157185 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155615, d157185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155615, d157185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155682 q = 1) (hb : d157243 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155682, d157243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155682, d157243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30530 (p : Pattern) (ha : d155683 p = 1) (hb : d157244 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155583 q = 1) (hb : d157153 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155583, d157153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155617 q = 1) (hb : d157187 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155617, d157187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155617, d157187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155618 q = 1) (hb : d157188 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155618, d157188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155618, d157188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155683 q = 1) (hb : d157244 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155683, d157244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155683, d157244, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30531 (p : Pattern) (ha : d155687 p = 1) (hb : d157248 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155649 q = 1) (hb : d157219 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155649, d157219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30521 q ha hb
    | true =>
      simp only [d155649, d157219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155650 q = 1) (hb : d157220 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155650, d157220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155650, d157220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155654 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155654, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30522 q ha hb
    | true =>
      simp only [d155654, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155655 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155655, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155655, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155656 q = 1) (hb : d157221 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155656, d157221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155656, d157221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155657 q = 1) (hb : d157222 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155657, d157222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155657, d157222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155658 q = 1) (hb : d157223 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155658, d157223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155658, d157223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155687 q = 1) (hb : d157248 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155687, d157248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155687, d157248, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30532 (p : Pattern) (ha : d155688 p = 1) (hb : d157165 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155654 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155654, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30522 q ha hb
    | true =>
      simp only [d155654, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155655 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155655, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155655, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155577 q = 1) (hb : d157147 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30506 q ha hb
    | true =>
      simp only [d155577, d157147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155578 q = 1) (hb : d157148 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155578, d157148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155660 q = 1) (hb : d157149 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155660, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155660, d157149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155661 q = 1) (hb : d157150 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155661, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155661, d157150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155662 q = 1) (hb : d157151 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155662, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155662, d157151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155688 q = 1) (hb : d157165 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155688, d157165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155688, d157165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30533 (p : Pattern) (ha : d155691 p = 1) (hb : d157251 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155573 q = 1) (hb : d157143 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30505 q ha hb
    | true =>
      simp only [d155573, d157143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155574 q = 1) (hb : d157144 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155574, d157144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155666 q = 1) (hb : d157227 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155666, d157227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155666, d157227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155667 q = 1) (hb : d157228 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155667, d157228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155667, d157228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155668 q = 1) (hb : d157229 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155668, d157229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155668, d157229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155691 q = 1) (hb : d157251 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155691, d157251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155691, d157251, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30534 (p : Pattern) (ha : d155697 p = 1) (hb : d157257 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155610 q = 1) (hb : d157180 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155610, d157180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30513 q ha hb
    | true =>
      simp only [d155610, d157180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30514 q ha hb
  have h2 (q : Pattern) (ha : d155611 q = 1) (hb : d157181 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155611, d157181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155611, d157181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155612 q = 1) (hb : d157182 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155612, d157182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155612, d157182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155613 q = 1) (hb : d157183 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155613, d157183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155613, d157183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155620 q = 1) (hb : d157190 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155620, d157190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30515 q ha hb
    | true =>
      simp only [d155620, d157190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30516 q ha hb
  have h6 (q : Pattern) (ha : d155621 q = 1) (hb : d157191 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155621, d157191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155621, d157191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155622 q = 1) (hb : d157192 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155622, d157192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155622, d157192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155664 q = 1) (hb : d157225 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155664, d157225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30523 q ha hb
    | true =>
      simp only [d155664, d157225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30524 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155587 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155665 q = 1) (hb : d157226 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155665, d157226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155665, d157226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d155670 q = 1) (hb : d157231 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155670, d157231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30525 q ha hb
    | true =>
      simp only [d155670, d157231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155671 q = 1) (hb : d157232 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155671, d157232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155671, d157232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155672 q = 1) (hb : d157233 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155672, d157233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155672, d157233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155673 q = 1) (hb : d157234 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155673, d157234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155673, d157234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155674 q = 1) (hb : d157235 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155674, d157235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155674, d157235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155678 q = 1) (hb : d157239 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155678, d157239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30527 q ha hb
    | true =>
      simp only [d155678, d157239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30528 q ha hb
  have h17 (q : Pattern) (ha : d155679 q = 1) (hb : d157240 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155679, d157240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155679, d157240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155680 q = 1) (hb : d157241 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155680, d157241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155680, d157241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d155681 q = 1) (hb : d157242 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155681, d157242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155681, d157242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d155684 q = 1) (hb : d157245 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155684, d157245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30529 q ha hb
    | true =>
      simp only [d155684, d157245, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30530 q ha hb
  have h21 (q : Pattern) (ha : d155685 q = 1) (hb : d157246 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155685, d157246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155685, d157246, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d155686 q = 1) (hb : d157247 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155686, d157247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d155686, d157247, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d155689 q = 1) (hb : d157249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155689, d157249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30531 q ha hb
    | true =>
      simp only [d155689, d157249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30532 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d155597 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d155690 q = 1) (hb : d157250 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155690, d157250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d155690, d157250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d155692 q = 1) (hb : d157252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155692, d157252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30533 q ha hb
    | true =>
      simp only [d155692, d157252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d155693 q = 1) (hb : d157253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155693, d157253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d155693, d157253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d155694 q = 1) (hb : d157254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155694, d157254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d155694, d157254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d155695 q = 1) (hb : d157255 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155695, d157255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d155695, d157255, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d155696 q = 1) (hb : d157256 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155696, d157256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d155696, d157256, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d155697 q = 1) (hb : d157257 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155697, d157257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155697, d157257, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro30535 (p : Pattern) (ha : d155709 p = 1) (hb : d157264 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155699 q = 1) (hb : d157157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155699, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30524 q ha hb
    | true =>
      simp only [d155699, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30508 q ha hb
  have h2 (q : Pattern) (ha : d155700 q = 1) (hb : d157158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155700, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155700, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155701 q = 1) (hb : d157159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155701, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155701, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155702 q = 1) (hb : d157160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155702, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155702, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155703 q = 1) (hb : d157161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155703, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155703, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155704 q = 1) (hb : d157259 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155704, d157259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30508 q ha hb
    | true =>
      simp only [d155704, d157259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155705 q = 1) (hb : d157260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155705, d157260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155705, d157260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155706 q = 1) (hb : d157261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155706, d157261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155706, d157261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155707 q = 1) (hb : d157262 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155707, d157262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155707, d157262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155708 q = 1) (hb : d157263 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155708, d157263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155708, d157263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155709 q = 1) (hb : d157264 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155709, d157264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155709, d157264, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30536 (p : Pattern) (ha : d155715 p = 1) (hb : d157270 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155704 q = 1) (hb : d157259 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155704, d157259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30508 q ha hb
    | true =>
      simp only [d155704, d157259, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155705 q = 1) (hb : d157260 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155705, d157260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155705, d157260, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155706 q = 1) (hb : d157261 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155706, d157261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155706, d157261, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155707 q = 1) (hb : d157262 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155707, d157262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155707, d157262, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155708 q = 1) (hb : d157263 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155708, d157263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155708, d157263, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155710 q = 1) (hb : d157265 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155710, d157265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30511 q ha hb
    | true =>
      simp only [d155710, d157265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155711 q = 1) (hb : d157266 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155711, d157266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155711, d157266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155712 q = 1) (hb : d157267 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155712, d157267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155712, d157267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155713 q = 1) (hb : d157268 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155713, d157268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155713, d157268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155714 q = 1) (hb : d157269 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155714, d157269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155714, d157269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155715 q = 1) (hb : d157270 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155715, d157270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155715, d157270, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30537 (p : Pattern) (ha : d155722 p = 1) (hb : d157277 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155689 q = 1) (hb : d157249 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155689, d157249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30531 q ha hb
    | true =>
      simp only [d155689, d157249, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30532 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155597 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155690 q = 1) (hb : d157250 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155690, d157250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155690, d157250, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d155692 q = 1) (hb : d157252 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155692, d157252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30533 q ha hb
    | true =>
      simp only [d155692, d157252, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155693 q = 1) (hb : d157253 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155693, d157253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155693, d157253, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155694 q = 1) (hb : d157254 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155694, d157254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155694, d157254, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155720 q = 1) (hb : d157275 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155720, d157275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155720, d157275, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155721 q = 1) (hb : d157276 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155721, d157276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155721, d157276, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155722 q = 1) (hb : d157277 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155722, d157277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155722, d157277, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30538 (p : Pattern) (ha : d155724 p = 1) (hb : d157279 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155710 q = 1) (hb : d157265 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155710, d157265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30511 q ha hb
    | true =>
      simp only [d155710, d157265, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155711 q = 1) (hb : d157266 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155711, d157266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155711, d157266, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155712 q = 1) (hb : d157267 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155712, d157267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155712, d157267, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155713 q = 1) (hb : d157268 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155713, d157268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155713, d157268, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155714 q = 1) (hb : d157269 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155714, d157269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155714, d157269, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155724 q = 1) (hb : d157279 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155724, d157279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155724, d157279, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30539 (p : Pattern) (ha : d155740 p = 1) (hb : d157294 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155730 q = 1) (hb : d157285 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155730, d157285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155730, d157285, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30517 q ha hb
  have h2 (q : Pattern) (ha : d155625 q = 1) (hb : d157194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155625, d157194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30517 q ha hb
    | true =>
      simp only [d155625, d157194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155731 q = 1) (hb : d157286 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155731, d157286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155731, d157286, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155626 q = 1) (hb : d157195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155626, d157195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155626, d157195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155732 q = 1) (hb : d157287 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155732, d157287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155732, d157287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155733 q = 1) (hb : d157288 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155733, d157288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155733, d157288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155734 q = 1) (hb : d157289 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155734, d157289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155734, d157289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30497 q ha hb
  have h8 (q : Pattern) (ha : d155529 q = 1) (hb : d157113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155529, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30497 q ha hb
    | true =>
      simp only [d155529, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155735 q = 1) (hb : d157290 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155735, d157290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155735, d157290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155530 q = 1) (hb : d157114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155530, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155530, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d155736 q = 1) (hb : d157291 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155736, d157291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155736, d157291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155737 q = 1) (hb : d157292 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155737, d157292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155737, d157292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155738 q = 1) (hb : d157293 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155738, d157293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155738, d157293, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155739 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155740 q = 1) (hb : d157294 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155740, d157294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155740, d157294, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro30540 (p : Pattern) (ha : d155746 p = 1) (hb : d157300 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155734 q = 1) (hb : d157289 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155734, d157289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155734, d157289, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30497 q ha hb
  have h2 (q : Pattern) (ha : d155529 q = 1) (hb : d157113 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155529, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30497 q ha hb
    | true =>
      simp only [d155529, d157113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155735 q = 1) (hb : d157290 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155735, d157290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155735, d157290, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155530 q = 1) (hb : d157114 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155530, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155530, d157114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155736 q = 1) (hb : d157291 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155736, d157291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155736, d157291, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155737 q = 1) (hb : d157292 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155737, d157292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155737, d157292, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155741 q = 1) (hb : d157295 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155741, d157295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155741, d157295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30498 q ha hb
  have h8 (q : Pattern) (ha : d155535 q = 1) (hb : d157118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155535, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30498 q ha hb
    | true =>
      simp only [d155535, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155742 q = 1) (hb : d157296 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155742, d157296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155742, d157296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155536 q = 1) (hb : d157119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155536, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155536, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d155743 q = 1) (hb : d157297 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155743, d157297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155743, d157297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155744 q = 1) (hb : d157298 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155744, d157298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155744, d157298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155745 q = 1) (hb : d157299 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155745, d157299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155745, d157299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155458 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155746 q = 1) (hb : d157300 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155746, d157300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155746, d157300, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro30541 (p : Pattern) (ha : d155756 p = 1) (hb : d157309 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155750 q = 1) (hb : d157304 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155750, d157304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155750, d157304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30519 q ha hb
  have h2 (q : Pattern) (ha : d155637 q = 1) (hb : d157207 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155637, d157207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30519 q ha hb
    | true =>
      simp only [d155637, d157207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155751 q = 1) (hb : d157305 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155751, d157305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155751, d157305, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155638 q = 1) (hb : d157208 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155638, d157208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155638, d157208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155752 q = 1) (hb : d157306 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155752, d157306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155752, d157306, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155753 q = 1) (hb : d157307 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155753, d157307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155753, d157307, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d155259 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d155754 q = 1) (hb : d157308 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155754, d157308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155754, d157308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155755 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155756 q = 1) (hb : d157309 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155756, d157309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155756, d157309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro30542 (p : Pattern) (ha : d155766 p = 1) (hb : d157319 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155741 q = 1) (hb : d157295 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155741, d157295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155741, d157295, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30498 q ha hb
  have h2 (q : Pattern) (ha : d155535 q = 1) (hb : d157118 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155535, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30498 q ha hb
    | true =>
      simp only [d155535, d157118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155742 q = 1) (hb : d157296 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155742, d157296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155742, d157296, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155536 q = 1) (hb : d157119 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155536, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155536, d157119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155743 q = 1) (hb : d157297 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155743, d157297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155743, d157297, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155744 q = 1) (hb : d157298 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155744, d157298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155744, d157298, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155761 q = 1) (hb : d157314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155761, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155761, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30500 q ha hb
  have h8 (q : Pattern) (ha : d155543 q = 1) (hb : d157125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155543, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30500 q ha hb
    | true =>
      simp only [d155543, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155762 q = 1) (hb : d157315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155762, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155762, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155544 q = 1) (hb : d157126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155544, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155544, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d155763 q = 1) (hb : d157316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155763, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155763, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155764 q = 1) (hb : d157317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155764, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155764, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d155765 q = 1) (hb : d157318 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155765, d157318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155765, d157318, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155755 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155766 q = 1) (hb : d157319 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155766, d157319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155766, d157319, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro30543 (p : Pattern) (ha : d155775 p = 1) (hb : d157324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155770 q = 1) (hb : d157314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155770, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155770, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30502 q ha hb
  have h2 (q : Pattern) (ha : d155555 q = 1) (hb : d157125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155555, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30502 q ha hb
    | true =>
      simp only [d155555, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155771 q = 1) (hb : d157315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155771, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155771, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155556 q = 1) (hb : d157126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155556, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155556, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155772 q = 1) (hb : d157316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155772, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155772, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155773 q = 1) (hb : d157317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155773, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155773, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155774 q = 1) (hb : d157323 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155774, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155774, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155775 q = 1) (hb : d157324 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155775, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155775, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30544 (p : Pattern) (ha : d155781 p = 1) (hb : d157330 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155747 q = 1) (hb : d157301 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155747, d157301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30539 q ha hb
    | true =>
      simp only [d155747, d157301, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30540 q ha hb
  have h2 (q : Pattern) (ha : d155748 q = 1) (hb : d157302 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155748, d157302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155748, d157302, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155749 q = 1) (hb : d157303 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155749, d157303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155749, d157303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155757 q = 1) (hb : d157310 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155757, d157310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30540 q ha hb
    | true =>
      simp only [d155757, d157310, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30541 q ha hb
  have h5 (q : Pattern) (ha : d155758 q = 1) (hb : d157311 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155758, d157311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155758, d157311, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155759 q = 1) (hb : d157312 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155759, d157312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155759, d157312, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155760 q = 1) (hb : d157313 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155760, d157313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155760, d157313, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155767 q = 1) (hb : d157320 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155767, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30540 q ha hb
    | true =>
      simp only [d155767, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30542 q ha hb
  have h9 (q : Pattern) (ha : d155768 q = 1) (hb : d157321 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155768, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155768, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155769 q = 1) (hb : d157322 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155769, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155769, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155776 q = 1) (hb : d157325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155776, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30542 q ha hb
    | true =>
      simp only [d155776, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30543 q ha hb
  have h12 (q : Pattern) (ha : d155777 q = 1) (hb : d157326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155777, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155777, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155778 q = 1) (hb : d157327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155778, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155778, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155779 q = 1) (hb : d157328 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155779, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155779, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155780 q = 1) (hb : d157329 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155780, d157329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155780, d157329, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155781 q = 1) (hb : d157330 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155781, d157330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155781, d157330, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro30545 (p : Pattern) (ha : d155786 p = 1) (hb : d157335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155767 q = 1) (hb : d157320 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155767, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30540 q ha hb
    | true =>
      simp only [d155767, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30542 q ha hb
  have h2 (q : Pattern) (ha : d155768 q = 1) (hb : d157321 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155768, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155768, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155769 q = 1) (hb : d157322 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155769, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155769, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155776 q = 1) (hb : d157325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155776, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30542 q ha hb
    | true =>
      simp only [d155776, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30543 q ha hb
  have h5 (q : Pattern) (ha : d155777 q = 1) (hb : d157326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155777, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155777, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155778 q = 1) (hb : d157327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155778, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155778, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155779 q = 1) (hb : d157328 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155779, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155779, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155784 q = 1) (hb : d157333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155784, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155784, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155785 q = 1) (hb : d157334 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155785, d157334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155785, d157334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155786 q = 1) (hb : d157335 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155786, d157335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155786, d157335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30546 (p : Pattern) (ha : d155792 p = 1) (hb : d157341 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155782 q = 1) (hb : d157331 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155782, d157331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30544 q ha hb
    | true =>
      simp only [d155782, d157331, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155783 q = 1) (hb : d157332 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155783, d157332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155783, d157332, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155787 q = 1) (hb : d157336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155787, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30545 q ha hb
    | true =>
      simp only [d155787, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155788 q = 1) (hb : d157337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155788, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155788, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155789 q = 1) (hb : d157338 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155789, d157338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155789, d157338, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155790 q = 1) (hb : d157339 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155790, d157339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155790, d157339, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155791 q = 1) (hb : d157340 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155791, d157340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155791, d157340, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155792 q = 1) (hb : d157341 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155792, d157341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155792, d157341, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30547 (p : Pattern) (ha : d155794 p = 1) (hb : d157324 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155761 q = 1) (hb : d157314 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155761, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155761, d157314, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30500 q ha hb
  have h2 (q : Pattern) (ha : d155543 q = 1) (hb : d157125 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155543, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30500 q ha hb
    | true =>
      simp only [d155543, d157125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155762 q = 1) (hb : d157315 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155762, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155762, d157315, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155544 q = 1) (hb : d157126 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155544, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155544, d157126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155763 q = 1) (hb : d157316 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155763, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155763, d157316, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155764 q = 1) (hb : d157317 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155764, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155764, d157317, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155793 q = 1) (hb : d157323 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155793, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155793, d157323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155794 q = 1) (hb : d157324 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155794, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155794, d157324, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30548 (p : Pattern) (ha : d155800 p = 1) (hb : d157343 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155795 q = 1) (hb : d157325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155795, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30542 q ha hb
    | true =>
      simp only [d155795, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30547 q ha hb
  have h2 (q : Pattern) (ha : d155796 q = 1) (hb : d157326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155796, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155796, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155797 q = 1) (hb : d157327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155797, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155797, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155798 q = 1) (hb : d157333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155798, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155798, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155799 q = 1) (hb : d157342 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155799, d157342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155799, d157342, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155800 q = 1) (hb : d157343 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155800, d157343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155800, d157343, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30549 (p : Pattern) (ha : d155806 p = 1) (hb : d157349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155787 q = 1) (hb : d157336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155787, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30545 q ha hb
    | true =>
      simp only [d155787, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155788 q = 1) (hb : d157337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155788, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155788, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155801 q = 1) (hb : d157344 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155801, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30548 q ha hb
    | true =>
      simp only [d155801, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155802 q = 1) (hb : d157345 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155802, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155802, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155803 q = 1) (hb : d157346 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155803, d157346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155803, d157346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155804 q = 1) (hb : d157347 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155804, d157347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155804, d157347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155805 q = 1) (hb : d157348 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155805, d157348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155805, d157348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155806 q = 1) (hb : d157349 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155806, d157349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155806, d157349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30550 (p : Pattern) (ha : d155809 p = 1) (hb : d157335 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155767 q = 1) (hb : d157320 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155767, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30540 q ha hb
    | true =>
      simp only [d155767, d157320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30542 q ha hb
  have h2 (q : Pattern) (ha : d155768 q = 1) (hb : d157321 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155768, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155768, d157321, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155769 q = 1) (hb : d157322 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155769, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155769, d157322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155776 q = 1) (hb : d157325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155776, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30542 q ha hb
    | true =>
      simp only [d155776, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30543 q ha hb
  have h5 (q : Pattern) (ha : d155777 q = 1) (hb : d157326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155777, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155777, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155778 q = 1) (hb : d157327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155778, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155778, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155779 q = 1) (hb : d157328 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155779, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155779, d157328, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155795 q = 1) (hb : d157325 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155795, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30542 q ha hb
    | true =>
      simp only [d155795, d157325, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30547 q ha hb
  have h9 (q : Pattern) (ha : d155796 q = 1) (hb : d157326 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155796, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155796, d157326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155797 q = 1) (hb : d157327 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155797, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155797, d157327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155798 q = 1) (hb : d157333 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155798, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155798, d157333, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155808 q = 1) (hb : d157334 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155808, d157334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155808, d157334, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155809 q = 1) (hb : d157335 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155809, d157335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155809, d157335, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro30551 (p : Pattern) (ha : d155825 p = 1) (hb : d157355 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155810 q = 1) (hb : d157336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155810, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30550 q ha hb
    | true =>
      simp only [d155810, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155811 q = 1) (hb : d157337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155811, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155811, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155822 q = 1) (hb : d157352 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155822, d157352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155822, d157352, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155823 q = 1) (hb : d157353 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155823, d157353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155823, d157353, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155824 q = 1) (hb : d157354 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155824, d157354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155824, d157354, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155825 q = 1) (hb : d157355 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155825, d157355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155825, d157355, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30552 (p : Pattern) (ha : d155831 p = 1) (hb : d157361 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155807 q = 1) (hb : d157350 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155807, d157350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30546 q ha hb
    | true =>
      simp only [d155807, d157350, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30549 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155820 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155821 q = 1) (hb : d157351 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155821, d157351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155821, d157351, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d155826 q = 1) (hb : d157356 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155826, d157356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30551 q ha hb
    | true =>
      simp only [d155826, d157356, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155827 q = 1) (hb : d157357 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155827, d157357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155827, d157357, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155828 q = 1) (hb : d157358 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155828, d157358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155828, d157358, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155829 q = 1) (hb : d157359 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155829, d157359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155829, d157359, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155830 q = 1) (hb : d157360 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155830, d157360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155830, d157360, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155831 q = 1) (hb : d157361 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155831, d157361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155831, d157361, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30553 (p : Pattern) (ha : d155819 p = 1) (hb : d157366 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155801 q = 1) (hb : d157344 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155801, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30548 q ha hb
    | true =>
      simp only [d155801, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155802 q = 1) (hb : d157345 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155802, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155802, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155816 q = 1) (hb : d157363 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155816, d157363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155816, d157363, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155817 q = 1) (hb : d157364 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155817, d157364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155817, d157364, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155818 q = 1) (hb : d157365 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155818, d157365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155818, d157365, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155819 q = 1) (hb : d157366 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155819, d157366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155819, d157366, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30554 (p : Pattern) (ha : d155838 p = 1) (hb : d157372 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155833 q = 1) (hb : d157367 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155833, d157367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30553 q ha hb
    | true =>
      simp only [d155833, d157367, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155834 q = 1) (hb : d157368 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155834, d157368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155834, d157368, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155835 q = 1) (hb : d157369 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155835, d157369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155835, d157369, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155836 q = 1) (hb : d157370 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155836, d157370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155836, d157370, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155837 q = 1) (hb : d157371 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155837, d157371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155837, d157371, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155838 q = 1) (hb : d157372 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155838, d157372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155838, d157372, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30555 (p : Pattern) (ha : d155844 p = 1) (hb : d157378 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155593 q = 1) (hb : d157163 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155593, d157163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155593, d157163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30509 q ha hb
  have h2 (q : Pattern) (ha : d155594 q = 1) (hb : d157164 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155594, d157164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155594, d157164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155603 q = 1) (hb : d157173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155603, d157173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30509 q ha hb
    | true =>
      simp only [d155603, d157173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30512 q ha hb
  have h4 (q : Pattern) (ha : d155604 q = 1) (hb : d157174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155604, d157174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155604, d157174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155605 q = 1) (hb : d157175 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155605, d157175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155605, d157175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155698 q = 1) (hb : d157258 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155698, d157258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30526 q ha hb
    | true =>
      simp only [d155698, d157258, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30534 q ha hb
  have h7 (q : Pattern) (ha : d155716 q = 1) (hb : d157271 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155716, d157271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30535 q ha hb
    | true =>
      simp only [d155716, d157271, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30536 q ha hb
  have h8 (q : Pattern) (ha : d155717 q = 1) (hb : d157272 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155717, d157272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155717, d157272, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155718 q = 1) (hb : d157273 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155718, d157273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155718, d157273, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d155719 q = 1) (hb : d157274 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155719, d157274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155719, d157274, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155723 q = 1) (hb : d157278 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155723, d157278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155723, d157278, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30537 q ha hb
  have h12 (q : Pattern) (ha : d155725 q = 1) (hb : d157280 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155725, d157280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155725, d157280, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30538 q ha hb
  have h13 (q : Pattern) (ha : d155726 q = 1) (hb : d157281 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155726, d157281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155726, d157281, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155727 q = 1) (hb : d157282 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155727, d157282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155727, d157282, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d155728 q = 1) (hb : d157283 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155728, d157283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d155728, d157283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d155729 q = 1) (hb : d157284 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155729, d157284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155729, d157284, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d155832 q = 1) (hb : d157362 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155832, d157362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155832, d157362, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30552 q ha hb
  have h18 (q : Pattern) (ha : d155839 q = 1) (hb : d157373 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155839, d157373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155839, d157373, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30554 q ha hb
  have h19 (q : Pattern) (ha : d155840 q = 1) (hb : d157374 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155840, d157374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155840, d157374, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d155841 q = 1) (hb : d157375 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155841, d157375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d155841, d157375, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d155842 q = 1) (hb : d157376 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155842, d157376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d155842, d157376, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d155843 q = 1) (hb : d157377 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155843, d157377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d155843, d157377, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d155844 q = 1) (hb : d157378 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155844, d157378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155844, d157378, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30556 (p : Pattern) (ha : d155850 p = 1) (hb : d157384 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155845 q = 1) (hb : d157379 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155845, d157379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155845, d157379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30555 q ha hb
  have h2 (q : Pattern) (ha : d155846 q = 1) (hb : d157380 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155846, d157380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155846, d157380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155847 q = 1) (hb : d157381 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155847, d157381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155847, d157381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155848 q = 1) (hb : d157382 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155848, d157382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155848, d157382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155849 q = 1) (hb : d157383 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155849, d157383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155849, d157383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155850 q = 1) (hb : d157384 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155850, d157384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155850, d157384, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30557 (p : Pattern) (ha : d155855 p = 1) (hb : d157388 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1527 q = 1) (hb : d52968 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro199 q ha hb
    | true =>
      simp only [d1527, d52968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro200 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1528 q = 1) (hb : d52969 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1528, d52969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro147 q ha hb
  have h4 (q : Pattern) (ha : d1529 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1529, d52970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10051 q = 1) (hb : d52970 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1534 q = 1) (hb : d52975 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro201 q ha hb
    | true =>
      simp only [d1534, d52975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1535 q = 1) (hb : d52976 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1535, d52976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52976 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d26555 q = 1) (hb : d52976 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d26555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26556 q = 1) (hb : d155854 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26556, d155854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26556, d155854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26557 q = 1) (hb : d155855 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26557, d155855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26557, d155855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d155855 q = 1) (hb : d157388 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157388, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro30558 (p : Pattern) (ha : d155861 p = 1) (hb : d157393 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155861 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d1543 q = 1) (hb : d52984 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro202 q ha hb
    | true =>
      simp only [d1543, d52984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro203 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d1544 q = 1) (hb : d52985 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1544, d52985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro148 q ha hb
  have h4 (q : Pattern) (ha : d1545 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1545, d52986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26558 q = 1) (hb : d52986 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1549 q = 1) (hb : d52990 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro204 q ha hb
    | true =>
      simp only [d1549, d52990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d1550 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1550, d52991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d10081 q = 1) (hb : d52991 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d10081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26572 q = 1) (hb : d155860 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26572, d155860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26572, d155860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26573 q = 1) (hb : d155861 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26573, d155861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26573, d155861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d155861 q = 1) (hb : d157393 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157393, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro30559 (p : Pattern) (ha : d155874 p = 1) (hb : d157399 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155856 q = 1) (hb : d157389 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155856, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30557 q ha hb
    | true =>
      simp only [d155856, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155857 q = 1) (hb : d157390 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155857, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155857, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155858 q = 1) (hb : d157391 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155858, d157391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155858, d157391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155859 q = 1) (hb : d157392 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155859, d157392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155859, d157392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155862 q = 1) (hb : d157394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155862, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30558 q ha hb
    | true =>
      simp only [d155862, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155863 q = 1) (hb : d157395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155863, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155863, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155864 q = 1) (hb : d157396 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155864, d157396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155864, d157396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155865 q = 1) (hb : d157397 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155865, d157397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155865, d157397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155866 q = 1) (hb : d157398 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155866, d157398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155866, d157398, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155873 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d155874 q = 1) (hb : d157399 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155874, d157399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155874, d157399, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro30560 (p : Pattern) (ha : d155876 p = 1) (hb : d157402 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155876 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d52989 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1575 q = 1) (hb : d53001 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1575, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d1575, d53001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro206 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d1115 q = 1) (hb : d52696 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d1115, d52696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro1 q ha hb
  have h5 (q : Pattern) (ha : d1576 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1576, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1576, d53002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d1593 q = 1) (hb : d53002 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d1593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d1578 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155875 q = 1) (hb : d157400 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d155875, d157400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d155875, d157400, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d155876 q = 1) (hb : d157401 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d155876, d157401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155876, d157401, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d155876 q = 1) (hb : d157402 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157402, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro30561 (p : Pattern) (ha : d155883 p = 1) (hb : d157408 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155862 q = 1) (hb : d157394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155862, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30558 q ha hb
    | true =>
      simp only [d155862, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155863 q = 1) (hb : d157395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155863, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155863, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155864 q = 1) (hb : d157396 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155864, d157396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155864, d157396, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155865 q = 1) (hb : d157397 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155865, d157397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155865, d157397, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155877 q = 1) (hb : d157403 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155877, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30560 q ha hb
    | true =>
      simp only [d155877, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155878 q = 1) (hb : d157404 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155878, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155878, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155879 q = 1) (hb : d157405 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155879, d157405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155879, d157405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155880 q = 1) (hb : d157406 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155880, d157406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155880, d157406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155881 q = 1) (hb : d157407 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155881, d157407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155881, d157407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155882 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d155883 q = 1) (hb : d157408 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155883, d157408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155883, d157408, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
  exact h11 p ha hb
theorem andIntro30562 (p : Pattern) (ha : d155888 p = 1) (hb : d157412 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155888 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d69209 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5128 q = 1) (hb : d69210 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5128, d69210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5128, d69210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d5129 q = 1) (hb : d69211 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5129, d69211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5129, d69211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d69211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d26754 q = 1) (hb : d69211 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d26754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d1564 q = 1) (hb : d53005 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro207 q ha hb
    | true =>
      simp only [d1564, d53005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h8 (q : Pattern) (ha : d1565 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d1565, d53006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d1578 q = 1) (hb : d53006 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d1578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26755 q = 1) (hb : d155887 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26755, d155887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d26755, d155887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d26756 q = 1) (hb : d155888 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26756, d155888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d26756, d155888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h13 (q : Pattern) (ha : d155888 q = 1) (hb : d157412 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157412, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro30563 (p : Pattern) (ha : d155894 p = 1) (hb : d157418 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155889 q = 1) (hb : d157413 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155889, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30562 q ha hb
    | true =>
      simp only [d155889, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155890 q = 1) (hb : d157414 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155890, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155890, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155891 q = 1) (hb : d157415 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155891, d157415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155891, d157415, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155892 q = 1) (hb : d157416 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155892, d157416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155892, d157416, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155893 q = 1) (hb : d157417 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155893, d157417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155893, d157417, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155894 q = 1) (hb : d157418 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155894, d157418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155894, d157418, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30564 (p : Pattern) (ha : d155900 p = 1) (hb : d157424 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155877 q = 1) (hb : d157403 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155877, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30560 q ha hb
    | true =>
      simp only [d155877, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155878 q = 1) (hb : d157404 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155878, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155878, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155879 q = 1) (hb : d157405 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155879, d157405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155879, d157405, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155880 q = 1) (hb : d157406 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155880, d157406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155880, d157406, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155899 q = 1) (hb : d157423 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155899, d157423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155899, d157423, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155900 q = 1) (hb : d157424 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155900, d157424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155900, d157424, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30565 (p : Pattern) (ha : d155906 p = 1) (hb : d157430 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155884 q = 1) (hb : d157409 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155884, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30559 q ha hb
    | true =>
      simp only [d155884, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30561 q ha hb
  have h2 (q : Pattern) (ha : d155885 q = 1) (hb : d157410 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155885, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155885, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155886 q = 1) (hb : d157411 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155886, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155886, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155895 q = 1) (hb : d157419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155895, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30561 q ha hb
    | true =>
      simp only [d155895, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30563 q ha hb
  have h5 (q : Pattern) (ha : d155896 q = 1) (hb : d157420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155896, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155896, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155897 q = 1) (hb : d157421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155897, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155897, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155898 q = 1) (hb : d157422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155898, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155898, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155901 q = 1) (hb : d157425 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155901, d157425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30561 q ha hb
    | true =>
      simp only [d155901, d157425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30564 q ha hb
  have h9 (q : Pattern) (ha : d155902 q = 1) (hb : d157426 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155902, d157426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155902, d157426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155903 q = 1) (hb : d157427 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155903, d157427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155903, d157427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155904 q = 1) (hb : d157428 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155904, d157428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155904, d157428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d155905 q = 1) (hb : d157429 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155905, d157429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155905, d157429, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155906 q = 1) (hb : d157430 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155906, d157430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155906, d157430, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro30566 (p : Pattern) (ha : d155910 p = 1) (hb : d157434 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155901 q = 1) (hb : d157425 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155901, d157425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30561 q ha hb
    | true =>
      simp only [d155901, d157425, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30564 q ha hb
  have h2 (q : Pattern) (ha : d155902 q = 1) (hb : d157426 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155902, d157426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155902, d157426, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155903 q = 1) (hb : d157427 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155903, d157427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155903, d157427, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155904 q = 1) (hb : d157428 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155904, d157428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155904, d157428, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155909 q = 1) (hb : d157433 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155909, d157433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155909, d157433, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155910 q = 1) (hb : d157434 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155910, d157434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155910, d157434, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30567 (p : Pattern) (ha : d155916 p = 1) (hb : d157440 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155907 q = 1) (hb : d157431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30565 q ha hb
    | true =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155908 q = 1) (hb : d157432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155913 q = 1) (hb : d157437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155914 q = 1) (hb : d157438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155914, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155914, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155915 q = 1) (hb : d157439 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155915, d157439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155915, d157439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155916 q = 1) (hb : d157440 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155916, d157440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155916, d157440, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30568 (p : Pattern) (ha : d155920 p = 1) (hb : d157444 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155917 q = 1) (hb : d157441 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155918 q = 1) (hb : d157442 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155918, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155918, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155919 q = 1) (hb : d157443 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155919, d157443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155919, d157443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155920 q = 1) (hb : d157444 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155920, d157444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155920, d157444, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30569 (p : Pattern) (ha : d155926 p = 1) (hb : d157450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155921 q = 1) (hb : d157445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155921, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30567 q ha hb
    | true =>
      simp only [d155921, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30568 q ha hb
  have h2 (q : Pattern) (ha : d155922 q = 1) (hb : d157446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155922, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155922, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155923 q = 1) (hb : d157447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155923, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155923, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155924 q = 1) (hb : d157448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155924, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155924, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155925 q = 1) (hb : d157449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155925, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155925, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155926 q = 1) (hb : d157450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155926, d157450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155926, d157450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30570 (p : Pattern) (ha : d155929 p = 1) (hb : d157453 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155907 q = 1) (hb : d157431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30565 q ha hb
    | true =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155908 q = 1) (hb : d157432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155913 q = 1) (hb : d157437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155914 q = 1) (hb : d157438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155914, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155914, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155915 q = 1) (hb : d157439 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155915, d157439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155915, d157439, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155929 q = 1) (hb : d157453 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155929, d157453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155929, d157453, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30571 (p : Pattern) (ha : d155930 p = 1) (hb : d157454 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155917 q = 1) (hb : d157441 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155918 q = 1) (hb : d157442 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155918, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155918, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155919 q = 1) (hb : d157443 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155919, d157443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155919, d157443, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155930 q = 1) (hb : d157454 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155930, d157454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155930, d157454, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30572 (p : Pattern) (ha : d155936 p = 1) (hb : d157460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155921 q = 1) (hb : d157445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155921, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30567 q ha hb
    | true =>
      simp only [d155921, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30568 q ha hb
  have h2 (q : Pattern) (ha : d155922 q = 1) (hb : d157446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155922, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155922, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155923 q = 1) (hb : d157447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155923, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155923, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155924 q = 1) (hb : d157448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155924, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155924, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155925 q = 1) (hb : d157449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155925, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155925, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155931 q = 1) (hb : d157455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155931, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30570 q ha hb
    | true =>
      simp only [d155931, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30571 q ha hb
  have h7 (q : Pattern) (ha : d155932 q = 1) (hb : d157456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155932, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155932, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155933 q = 1) (hb : d157457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155933, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155933, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155934 q = 1) (hb : d157458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155934, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155934, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155935 q = 1) (hb : d157459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155935, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155935, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155936 q = 1) (hb : d157460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155936, d157460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155936, d157460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30573 (p : Pattern) (ha : d155941 p = 1) (hb : d157465 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155907 q = 1) (hb : d157431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30565 q ha hb
    | true =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155908 q = 1) (hb : d157432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155913 q = 1) (hb : d157437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155914 q = 1) (hb : d157438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155914, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155914, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155940 q = 1) (hb : d157464 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155940, d157464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155940, d157464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155941 q = 1) (hb : d157465 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155941, d157465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155941, d157465, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30574 (p : Pattern) (ha : d155943 p = 1) (hb : d157467 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155917 q = 1) (hb : d157441 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155918 q = 1) (hb : d157442 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155918, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155918, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155942 q = 1) (hb : d157466 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155942, d157466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155942, d157466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155943 q = 1) (hb : d157467 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155943, d157467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155943, d157467, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30575 (p : Pattern) (ha : d155950 p = 1) (hb : d157474 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155907 q = 1) (hb : d157431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30565 q ha hb
    | true =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155908 q = 1) (hb : d157432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155913 q = 1) (hb : d157437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155948 q = 1) (hb : d157472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155948, d157472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155948, d157472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155949 q = 1) (hb : d157473 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155949, d157473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155949, d157473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155950 q = 1) (hb : d157474 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155950, d157474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155950, d157474, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30576 (p : Pattern) (ha : d155953 p = 1) (hb : d157477 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155917 q = 1) (hb : d157441 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155951 q = 1) (hb : d157475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155951, d157475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155951, d157475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155952 q = 1) (hb : d157476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155952, d157476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155952, d157476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155953 q = 1) (hb : d157477 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155953, d157477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155953, d157477, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30577 (p : Pattern) (ha : d155958 p = 1) (hb : d157481 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155958 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d1200 q = 1) (hb : d52781 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro172 q ha hb
    | true =>
      simp only [d1200, d52781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d1201 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d1201, d52782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d10042 q = 1) (hb : d52782 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d10042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d1204 q = 1) (hb : d52785 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro173 q ha hb
    | true =>
      simp only [d1204, d52785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d1205 q = 1) (hb : d52786 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d1205, d52786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d52786 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d26185 q = 1) (hb : d52786 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d26185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d26185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d26186 q = 1) (hb : d155957 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d26186, d155957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d26186, d155957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d26187 q = 1) (hb : d155958 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d26187, d155958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d26187, d155958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d155958 q = 1) (hb : d157481 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157481, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro30578 (p : Pattern) (ha : d155964 p = 1) (hb : d157487 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155959 q = 1) (hb : d157482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155959, d157482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30577 q ha hb
    | true =>
      simp only [d155959, d157482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155960 q = 1) (hb : d157483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155960, d157483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155960, d157483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155961 q = 1) (hb : d157484 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155961, d157484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155961, d157484, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155962 q = 1) (hb : d157485 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155962, d157485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155962, d157485, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155856 q = 1) (hb : d157389 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155856, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30557 q ha hb
    | true =>
      simp only [d155856, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d155857 q = 1) (hb : d157390 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155857, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155857, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155858 q = 1) (hb : d157391 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155858, d157391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155858, d157391, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155859 q = 1) (hb : d157392 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155859, d157392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155859, d157392, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155963 q = 1) (hb : d157486 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155963, d157486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155963, d157486, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155964 q = 1) (hb : d157487 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155964, d157487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155964, d157487, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30579 (p : Pattern) (ha : d155969 p = 1) (hb : d157494 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155969 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d10055 q = 1) (hb : d101482 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d10055, d101482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro23340 q ha hb
  have h3 (q : Pattern) (ha : d10056 q = 1) (hb : d101483 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d10056, d101483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d101483 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d101483 q = 1) (hb : d157491 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d157491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d157491, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155968 q = 1) (hb : d157492 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d155968, d157492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155968, d157492, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h7 (q : Pattern) (ha : d155969 q = 1) (hb : d157493 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d155969, d157493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155969, d157493, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  have h8 (q : Pattern) (ha : d155969 q = 1) (hb : d157494 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157494, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30580 (p : Pattern) (ha : d155975 p = 1) (hb : d157500 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155970 q = 1) (hb : d157495 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155970, d157495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30579 q ha hb
    | true =>
      simp only [d155970, d157495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155971 q = 1) (hb : d157496 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155971, d157496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155971, d157496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155972 q = 1) (hb : d157497 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d155972, d157497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155972, d157497, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155973 q = 1) (hb : d157498 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d155973, d157498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155973, d157498, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d155872 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d155974 q = 1) (hb : d157499 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d155974, d157499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155974, d157499, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d155882 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d155975 q = 1) (hb : d157500 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d155975, d157500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155975, d157500, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  exact h8 p ha hb
theorem andIntro30581 (p : Pattern) (ha : d155981 p = 1) (hb : d157506 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155965 q = 1) (hb : d157488 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155965, d157488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30578 q ha hb
    | true =>
      simp only [d155965, d157488, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30559 q ha hb
  have h2 (q : Pattern) (ha : d155966 q = 1) (hb : d157489 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155966, d157489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155966, d157489, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155967 q = 1) (hb : d157490 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155967, d157490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155967, d157490, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155976 q = 1) (hb : d157501 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155976, d157501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30559 q ha hb
    | true =>
      simp only [d155976, d157501, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30580 q ha hb
  have h5 (q : Pattern) (ha : d155977 q = 1) (hb : d157502 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155977, d157502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155977, d157502, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155978 q = 1) (hb : d157503 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155978, d157503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155978, d157503, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155979 q = 1) (hb : d157504 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155979, d157504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155979, d157504, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155884 q = 1) (hb : d157409 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155884, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30559 q ha hb
    | true =>
      simp only [d155884, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30561 q ha hb
  have h9 (q : Pattern) (ha : d155885 q = 1) (hb : d157410 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155885, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155885, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155886 q = 1) (hb : d157411 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155886, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155886, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d155895 q = 1) (hb : d157419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155895, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30561 q ha hb
    | true =>
      simp only [d155895, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30563 q ha hb
  have h12 (q : Pattern) (ha : d155896 q = 1) (hb : d157420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155896, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155896, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155897 q = 1) (hb : d157421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155897, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155897, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d155898 q = 1) (hb : d157422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155898, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155898, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d155980 q = 1) (hb : d157505 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155980, d157505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155980, d157505, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d155981 q = 1) (hb : d157506 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155981, d157506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155981, d157506, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro30582 (p : Pattern) (ha : d155986 p = 1) (hb : d157511 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155884 q = 1) (hb : d157409 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155884, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30559 q ha hb
    | true =>
      simp only [d155884, d157409, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30561 q ha hb
  have h2 (q : Pattern) (ha : d155885 q = 1) (hb : d157410 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155885, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155885, d157410, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155886 q = 1) (hb : d157411 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155886, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155886, d157411, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155895 q = 1) (hb : d157419 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d155895, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30561 q ha hb
    | true =>
      simp only [d155895, d157419, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30563 q ha hb
  have h5 (q : Pattern) (ha : d155896 q = 1) (hb : d157420 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d155896, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155896, d157420, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155897 q = 1) (hb : d157421 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d155897, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155897, d157421, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155898 q = 1) (hb : d157422 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155898, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155898, d157422, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155984 q = 1) (hb : d157509 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d155984, d157509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155984, d157509, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d155985 q = 1) (hb : d157510 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d155985, d157510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155985, d157510, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155986 q = 1) (hb : d157511 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d155986, d157511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155986, d157511, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30583 (p : Pattern) (ha : d155992 p = 1) (hb : d157517 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155982 q = 1) (hb : d157507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155982, d157507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30581 q ha hb
    | true =>
      simp only [d155982, d157507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155983 q = 1) (hb : d157508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155983, d157508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155983, d157508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155987 q = 1) (hb : d157512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155987, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30582 q ha hb
    | true =>
      simp only [d155987, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155988 q = 1) (hb : d157513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155988, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155988, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155989 q = 1) (hb : d157514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155989, d157514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155989, d157514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155990 q = 1) (hb : d157515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155990, d157515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155990, d157515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155991 q = 1) (hb : d157516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155991, d157516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155991, d157516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155992 q = 1) (hb : d157517 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155992, d157517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155992, d157517, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30584 (p : Pattern) (ha : d155996 p = 1) (hb : d157521 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155987 q = 1) (hb : d157512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155987, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30582 q ha hb
    | true =>
      simp only [d155987, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155988 q = 1) (hb : d157513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155988, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155988, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155993 q = 1) (hb : d157518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155993, d157518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155993, d157518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155994 q = 1) (hb : d157519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155994, d157519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155994, d157519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155995 q = 1) (hb : d157520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155995, d157520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155995, d157520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155996 q = 1) (hb : d157521 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155996, d157521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155996, d157521, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30585 (p : Pattern) (ha : d156002 p = 1) (hb : d157527 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155907 q = 1) (hb : d157431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30565 q ha hb
    | true =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155908 q = 1) (hb : d157432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155999 q = 1) (hb : d157524 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155999, d157524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155999, d157524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156000 q = 1) (hb : d157525 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156000, d157525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156000, d157525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156001 q = 1) (hb : d157526 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156001, d157526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156001, d157526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156002 q = 1) (hb : d157527 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156002, d157527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156002, d157527, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30586 (p : Pattern) (ha : d156008 p = 1) (hb : d157533 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155944 q = 1) (hb : d157468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155944, d157468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30573 q ha hb
    | true =>
      simp only [d155944, d157468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30574 q ha hb
  have h2 (q : Pattern) (ha : d155945 q = 1) (hb : d157469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155945, d157469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155945, d157469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155946 q = 1) (hb : d157470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155946, d157470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155946, d157470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155947 q = 1) (hb : d157471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155947, d157471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155947, d157471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155954 q = 1) (hb : d157478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155954, d157478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30575 q ha hb
    | true =>
      simp only [d155954, d157478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30576 q ha hb
  have h6 (q : Pattern) (ha : d155955 q = 1) (hb : d157479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155955, d157479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155955, d157479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155956 q = 1) (hb : d157480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155956, d157480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155956, d157480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155997 q = 1) (hb : d157522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155997, d157522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30583 q ha hb
    | true =>
      simp only [d155997, d157522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30584 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155921 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155998 q = 1) (hb : d157523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155998, d157523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155998, d157523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d156003 q = 1) (hb : d157528 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156003, d157528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30585 q ha hb
    | true =>
      simp only [d156003, d157528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d156004 q = 1) (hb : d157529 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156004, d157529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156004, d157529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156005 q = 1) (hb : d157530 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156005, d157530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156005, d157530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156006 q = 1) (hb : d157531 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156006, d157531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156006, d157531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156007 q = 1) (hb : d157532 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156007, d157532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156007, d157532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156008 q = 1) (hb : d157533 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156008, d157533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156008, d157533, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro30587 (p : Pattern) (ha : d156009 p = 1) (hb : d157534 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155907 q = 1) (hb : d157431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30565 q ha hb
    | true =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155908 q = 1) (hb : d157432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155913 q = 1) (hb : d157437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155914 q = 1) (hb : d157438 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155914, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155914, d157438, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155940 q = 1) (hb : d157464 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155940, d157464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155940, d157464, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156009 q = 1) (hb : d157534 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156009, d157534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156009, d157534, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30588 (p : Pattern) (ha : d156010 p = 1) (hb : d157535 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155917 q = 1) (hb : d157441 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155918 q = 1) (hb : d157442 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155918, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155918, d157442, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155942 q = 1) (hb : d157466 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155942, d157466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155942, d157466, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156010 q = 1) (hb : d157535 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156010, d157535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156010, d157535, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30589 (p : Pattern) (ha : d156015 p = 1) (hb : d157540 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155907 q = 1) (hb : d157431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30565 q ha hb
    | true =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155908 q = 1) (hb : d157432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155913 q = 1) (hb : d157437 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155913, d157437, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155948 q = 1) (hb : d157472 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155948, d157472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155948, d157472, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155949 q = 1) (hb : d157473 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155949, d157473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155949, d157473, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156015 q = 1) (hb : d157540 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156015, d157540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156015, d157540, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30590 (p : Pattern) (ha : d156016 p = 1) (hb : d157541 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155917 q = 1) (hb : d157441 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155917, d157441, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155951 q = 1) (hb : d157475 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155951, d157475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155951, d157475, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155952 q = 1) (hb : d157476 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155952, d157476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155952, d157476, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156016 q = 1) (hb : d157541 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156016, d157541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156016, d157541, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30591 (p : Pattern) (ha : d156020 p = 1) (hb : d157545 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155982 q = 1) (hb : d157507 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155982, d157507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30581 q ha hb
    | true =>
      simp only [d155982, d157507, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155983 q = 1) (hb : d157508 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155983, d157508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155983, d157508, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155987 q = 1) (hb : d157512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155987, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30582 q ha hb
    | true =>
      simp only [d155987, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155988 q = 1) (hb : d157513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155988, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155988, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155989 q = 1) (hb : d157514 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155989, d157514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155989, d157514, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155990 q = 1) (hb : d157515 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155990, d157515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155990, d157515, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155991 q = 1) (hb : d157516 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155991, d157516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155991, d157516, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156020 q = 1) (hb : d157545 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156020, d157545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156020, d157545, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30592 (p : Pattern) (ha : d156021 p = 1) (hb : d157546 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155987 q = 1) (hb : d157512 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155987, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30582 q ha hb
    | true =>
      simp only [d155987, d157512, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155988 q = 1) (hb : d157513 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155988, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155988, d157513, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155911 q = 1) (hb : d157435 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30566 q ha hb
    | true =>
      simp only [d155911, d157435, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155912 q = 1) (hb : d157436 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155912, d157436, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155993 q = 1) (hb : d157518 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155993, d157518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155993, d157518, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155994 q = 1) (hb : d157519 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155994, d157519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155994, d157519, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155995 q = 1) (hb : d157520 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155995, d157520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155995, d157520, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156021 q = 1) (hb : d157546 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156021, d157546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156021, d157546, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30593 (p : Pattern) (ha : d156024 p = 1) (hb : d157549 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155907 q = 1) (hb : d157431 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30565 q ha hb
    | true =>
      simp only [d155907, d157431, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155908 q = 1) (hb : d157432 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155908, d157432, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155999 q = 1) (hb : d157524 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155999, d157524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155999, d157524, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156000 q = 1) (hb : d157525 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156000, d157525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156000, d157525, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156001 q = 1) (hb : d157526 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156001, d157526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156001, d157526, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156024 q = 1) (hb : d157549 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156024, d157549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156024, d157549, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30594 (p : Pattern) (ha : d156030 p = 1) (hb : d157555 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155944 q = 1) (hb : d157468 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155944, d157468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30573 q ha hb
    | true =>
      simp only [d155944, d157468, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30574 q ha hb
  have h2 (q : Pattern) (ha : d155945 q = 1) (hb : d157469 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155945, d157469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155945, d157469, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155946 q = 1) (hb : d157470 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155946, d157470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155946, d157470, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155947 q = 1) (hb : d157471 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155947, d157471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155947, d157471, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155954 q = 1) (hb : d157478 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155954, d157478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30575 q ha hb
    | true =>
      simp only [d155954, d157478, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30576 q ha hb
  have h6 (q : Pattern) (ha : d155955 q = 1) (hb : d157479 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155955, d157479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155955, d157479, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155956 q = 1) (hb : d157480 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155956, d157480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155956, d157480, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155997 q = 1) (hb : d157522 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155997, d157522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30583 q ha hb
    | true =>
      simp only [d155997, d157522, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30584 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155921 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d155998 q = 1) (hb : d157523 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155998, d157523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155998, d157523, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d156003 q = 1) (hb : d157528 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156003, d157528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30585 q ha hb
    | true =>
      simp only [d156003, d157528, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d156004 q = 1) (hb : d157529 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156004, d157529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156004, d157529, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156005 q = 1) (hb : d157530 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156005, d157530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156005, d157530, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156006 q = 1) (hb : d157531 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156006, d157531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156006, d157531, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156007 q = 1) (hb : d157532 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156007, d157532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156007, d157532, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156011 q = 1) (hb : d157536 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156011, d157536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30587 q ha hb
    | true =>
      simp only [d156011, d157536, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30588 q ha hb
  have h17 (q : Pattern) (ha : d156012 q = 1) (hb : d157537 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156012, d157537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156012, d157537, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156013 q = 1) (hb : d157538 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156013, d157538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d156013, d157538, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d156014 q = 1) (hb : d157539 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156014, d157539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156014, d157539, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d156017 q = 1) (hb : d157542 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156017, d157542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30589 q ha hb
    | true =>
      simp only [d156017, d157542, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30590 q ha hb
  have h21 (q : Pattern) (ha : d156018 q = 1) (hb : d157543 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156018, d157543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156018, d157543, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d156019 q = 1) (hb : d157544 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156019, d157544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d156019, d157544, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d156022 q = 1) (hb : d157547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156022, d157547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30591 q ha hb
    | true =>
      simp only [d156022, d157547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30592 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d155931 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d156023 q = 1) (hb : d157548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156023, d157548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d156023, d157548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d156025 q = 1) (hb : d157550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156025, d157550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30593 q ha hb
    | true =>
      simp only [d156025, d157550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d156026 q = 1) (hb : d157551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156026, d157551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d156026, d157551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d156027 q = 1) (hb : d157552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156027, d157552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d156027, d157552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d156028 q = 1) (hb : d157553 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156028, d157553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d156028, d157553, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d156029 q = 1) (hb : d157554 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156029, d157554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d156029, d157554, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d156030 q = 1) (hb : d157555 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156030, d157555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156030, d157555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro30595 (p : Pattern) (ha : d156042 p = 1) (hb : d157567 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156032 q = 1) (hb : d157557 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156032, d157557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30584 q ha hb
    | true =>
      simp only [d156032, d157557, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30568 q ha hb
  have h2 (q : Pattern) (ha : d156033 q = 1) (hb : d157558 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156033, d157558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156033, d157558, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156034 q = 1) (hb : d157559 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156034, d157559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156034, d157559, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156035 q = 1) (hb : d157560 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156035, d157560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156035, d157560, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156036 q = 1) (hb : d157561 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156036, d157561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156036, d157561, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156037 q = 1) (hb : d157562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156037, d157562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30568 q ha hb
    | true =>
      simp only [d156037, d157562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156038 q = 1) (hb : d157563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156038, d157563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156038, d157563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156039 q = 1) (hb : d157564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156039, d157564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156039, d157564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156040 q = 1) (hb : d157565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156040, d157565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156040, d157565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156041 q = 1) (hb : d157566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156041, d157566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156041, d157566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156042 q = 1) (hb : d157567 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156042, d157567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156042, d157567, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30596 (p : Pattern) (ha : d156048 p = 1) (hb : d157573 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156037 q = 1) (hb : d157562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156037, d157562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30568 q ha hb
    | true =>
      simp only [d156037, d157562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156038 q = 1) (hb : d157563 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156038, d157563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156038, d157563, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156039 q = 1) (hb : d157564 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156039, d157564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156039, d157564, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156040 q = 1) (hb : d157565 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156040, d157565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156040, d157565, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156041 q = 1) (hb : d157566 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156041, d157566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156041, d157566, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156043 q = 1) (hb : d157568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156043, d157568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30571 q ha hb
    | true =>
      simp only [d156043, d157568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156044 q = 1) (hb : d157569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156044, d157569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156044, d157569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156045 q = 1) (hb : d157570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156045, d157570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156045, d157570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156046 q = 1) (hb : d157571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156046, d157571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156046, d157571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156047 q = 1) (hb : d157572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156047, d157572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156047, d157572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156048 q = 1) (hb : d157573 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156048, d157573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156048, d157573, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30597 (p : Pattern) (ha : d156055 p = 1) (hb : d157580 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156022 q = 1) (hb : d157547 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156022, d157547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30591 q ha hb
    | true =>
      simp only [d156022, d157547, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30592 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155931 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156023 q = 1) (hb : d157548 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156023, d157548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156023, d157548, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d156025 q = 1) (hb : d157550 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156025, d157550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30593 q ha hb
    | true =>
      simp only [d156025, d157550, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156026 q = 1) (hb : d157551 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156026, d157551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156026, d157551, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156027 q = 1) (hb : d157552 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156027, d157552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156027, d157552, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156053 q = 1) (hb : d157578 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156053, d157578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156053, d157578, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156054 q = 1) (hb : d157579 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156054, d157579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156054, d157579, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156055 q = 1) (hb : d157580 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156055, d157580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156055, d157580, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30598 (p : Pattern) (ha : d156057 p = 1) (hb : d157582 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156043 q = 1) (hb : d157568 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156043, d157568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30571 q ha hb
    | true =>
      simp only [d156043, d157568, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156044 q = 1) (hb : d157569 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156044, d157569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156044, d157569, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156045 q = 1) (hb : d157570 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156045, d157570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156045, d157570, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156046 q = 1) (hb : d157571 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156046, d157571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156046, d157571, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156047 q = 1) (hb : d157572 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156047, d157572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156047, d157572, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156057 q = 1) (hb : d157582 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156057, d157582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156057, d157582, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30599 (p : Pattern) (ha : d156072 p = 1) (hb : d157597 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156063 q = 1) (hb : d157588 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156063, d157588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156063, d157588, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30577 q ha hb
  have h2 (q : Pattern) (ha : d155959 q = 1) (hb : d157482 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155959, d157482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30577 q ha hb
    | true =>
      simp only [d155959, d157482, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156064 q = 1) (hb : d157589 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156064, d157589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156064, d157589, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155960 q = 1) (hb : d157483 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155960, d157483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155960, d157483, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156065 q = 1) (hb : d157590 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156065, d157590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156065, d157590, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156066 q = 1) (hb : d157591 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156066, d157591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156066, d157591, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156067 q = 1) (hb : d157592 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156067, d157592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156067, d157592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30557 q ha hb
  have h8 (q : Pattern) (ha : d155856 q = 1) (hb : d157389 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155856, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30557 q ha hb
    | true =>
      simp only [d155856, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156068 q = 1) (hb : d157593 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156068, d157593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156068, d157593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155857 q = 1) (hb : d157390 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155857, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155857, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d156069 q = 1) (hb : d157594 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156069, d157594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156069, d157594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156070 q = 1) (hb : d157595 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156070, d157595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156070, d157595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156071 q = 1) (hb : d157596 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156071, d157596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156071, d157596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156072 q = 1) (hb : d157597 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156072, d157597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156072, d157597, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro30600 (p : Pattern) (ha : d156083 p = 1) (hb : d157603 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156067 q = 1) (hb : d157592 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156067, d157592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156067, d157592, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30557 q ha hb
  have h2 (q : Pattern) (ha : d155856 q = 1) (hb : d157389 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155856, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30557 q ha hb
    | true =>
      simp only [d155856, d157389, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156068 q = 1) (hb : d157593 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156068, d157593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156068, d157593, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155857 q = 1) (hb : d157390 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155857, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155857, d157390, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156069 q = 1) (hb : d157594 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156069, d157594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156069, d157594, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156070 q = 1) (hb : d157595 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156070, d157595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156070, d157595, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156073 q = 1) (hb : d157598 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156073, d157598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156073, d157598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30558 q ha hb
  have h8 (q : Pattern) (ha : d155862 q = 1) (hb : d157394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155862, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30558 q ha hb
    | true =>
      simp only [d155862, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156074 q = 1) (hb : d157599 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156074, d157599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156074, d157599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155863 q = 1) (hb : d157395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155863, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155863, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d156075 q = 1) (hb : d157600 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156075, d157600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156075, d157600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156076 q = 1) (hb : d157601 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156076, d157601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156076, d157601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156077 q = 1) (hb : d157602 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156077, d157602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156077, d157602, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d156082 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156083 q = 1) (hb : d157603 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156083, d157603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156083, d157603, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro30601 (p : Pattern) (ha : d156093 p = 1) (hb : d157612 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156087 q = 1) (hb : d157607 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156087, d157607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156087, d157607, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30579 q ha hb
  have h2 (q : Pattern) (ha : d155970 q = 1) (hb : d157495 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155970, d157495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30579 q ha hb
    | true =>
      simp only [d155970, d157495, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156088 q = 1) (hb : d157608 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156088, d157608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156088, d157608, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155971 q = 1) (hb : d157496 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155971, d157496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155971, d157496, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156089 q = 1) (hb : d157609 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156089, d157609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156089, d157609, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156090 q = 1) (hb : d157610 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156090, d157610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156090, d157610, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d0 q = 1) (hb : d156081 q = 1) : d0 q = 1 := by
    exact ha
  have h8 (q : Pattern) (ha : d156091 q = 1) (hb : d157611 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156091, d157611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156091, d157611, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d156092 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d156093 q = 1) (hb : d157612 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156093, d157612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156093, d157612, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  exact h10 p ha hb
theorem andIntro30602 (p : Pattern) (ha : d156103 p = 1) (hb : d157622 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156073 q = 1) (hb : d157598 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156073, d157598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156073, d157598, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30558 q ha hb
  have h2 (q : Pattern) (ha : d155862 q = 1) (hb : d157394 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155862, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30558 q ha hb
    | true =>
      simp only [d155862, d157394, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156074 q = 1) (hb : d157599 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156074, d157599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156074, d157599, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155863 q = 1) (hb : d157395 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155863, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155863, d157395, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156075 q = 1) (hb : d157600 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156075, d157600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156075, d157600, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156076 q = 1) (hb : d157601 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156076, d157601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156076, d157601, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156098 q = 1) (hb : d157617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156098, d157617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156098, d157617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30560 q ha hb
  have h8 (q : Pattern) (ha : d155877 q = 1) (hb : d157403 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155877, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30560 q ha hb
    | true =>
      simp only [d155877, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156099 q = 1) (hb : d157618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156099, d157618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156099, d157618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155878 q = 1) (hb : d157404 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155878, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155878, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d156100 q = 1) (hb : d157619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156100, d157619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156100, d157619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156101 q = 1) (hb : d157620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156101, d157620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156101, d157620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156102 q = 1) (hb : d157621 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156102, d157621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156102, d157621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d156092 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156103 q = 1) (hb : d157622 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156103, d157622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156103, d157622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  exact h15 p ha hb
theorem andIntro30603 (p : Pattern) (ha : d156112 p = 1) (hb : d157631 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156107 q = 1) (hb : d157626 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156107, d157626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156107, d157626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30562 q ha hb
  have h2 (q : Pattern) (ha : d155889 q = 1) (hb : d157413 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155889, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30562 q ha hb
    | true =>
      simp only [d155889, d157413, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156108 q = 1) (hb : d157627 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156108, d157627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156108, d157627, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155890 q = 1) (hb : d157414 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155890, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155890, d157414, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156109 q = 1) (hb : d157628 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156109, d157628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156109, d157628, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156110 q = 1) (hb : d157629 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156110, d157629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156110, d157629, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156111 q = 1) (hb : d157630 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156111, d157630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156111, d157630, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156112 q = 1) (hb : d157631 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156112, d157631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156112, d157631, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30604 (p : Pattern) (ha : d156118 p = 1) (hb : d157637 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156084 q = 1) (hb : d157604 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156084, d157604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30599 q ha hb
    | true =>
      simp only [d156084, d157604, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30600 q ha hb
  have h2 (q : Pattern) (ha : d156085 q = 1) (hb : d157605 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156085, d157605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156085, d157605, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156086 q = 1) (hb : d157606 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156086, d157606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156086, d157606, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156094 q = 1) (hb : d157613 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156094, d157613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30600 q ha hb
    | true =>
      simp only [d156094, d157613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30601 q ha hb
  have h5 (q : Pattern) (ha : d156095 q = 1) (hb : d157614 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156095, d157614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156095, d157614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156096 q = 1) (hb : d157615 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156096, d157615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156096, d157615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156097 q = 1) (hb : d157616 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156097, d157616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156097, d157616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156104 q = 1) (hb : d157623 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156104, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30600 q ha hb
    | true =>
      simp only [d156104, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30602 q ha hb
  have h9 (q : Pattern) (ha : d156105 q = 1) (hb : d157624 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156105, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156105, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156106 q = 1) (hb : d157625 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156106, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156106, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156113 q = 1) (hb : d157632 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156113, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30602 q ha hb
    | true =>
      simp only [d156113, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30603 q ha hb
  have h12 (q : Pattern) (ha : d156114 q = 1) (hb : d157633 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156114, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156114, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156115 q = 1) (hb : d157634 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156115, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156115, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156116 q = 1) (hb : d157635 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156116, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156116, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156117 q = 1) (hb : d157636 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156117, d157636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156117, d157636, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156118 q = 1) (hb : d157637 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156118, d157637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156118, d157637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro30605 (p : Pattern) (ha : d156123 p = 1) (hb : d157642 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156104 q = 1) (hb : d157623 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156104, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30600 q ha hb
    | true =>
      simp only [d156104, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30602 q ha hb
  have h2 (q : Pattern) (ha : d156105 q = 1) (hb : d157624 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156105, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156105, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156106 q = 1) (hb : d157625 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156106, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156106, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156113 q = 1) (hb : d157632 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156113, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30602 q ha hb
    | true =>
      simp only [d156113, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30603 q ha hb
  have h5 (q : Pattern) (ha : d156114 q = 1) (hb : d157633 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156114, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156114, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156115 q = 1) (hb : d157634 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156115, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156115, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156116 q = 1) (hb : d157635 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156116, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156116, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156121 q = 1) (hb : d157640 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156121, d157640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156121, d157640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156122 q = 1) (hb : d157641 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156122, d157641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156122, d157641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156123 q = 1) (hb : d157642 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156123, d157642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156123, d157642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30606 (p : Pattern) (ha : d156129 p = 1) (hb : d157648 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156119 q = 1) (hb : d157638 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156119, d157638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30604 q ha hb
    | true =>
      simp only [d156119, d157638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156120 q = 1) (hb : d157639 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156120, d157639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156120, d157639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156124 q = 1) (hb : d157643 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156124, d157643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30605 q ha hb
    | true =>
      simp only [d156124, d157643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156125 q = 1) (hb : d157644 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156125, d157644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156125, d157644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156126 q = 1) (hb : d157645 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156126, d157645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156126, d157645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156127 q = 1) (hb : d157646 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156127, d157646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156127, d157646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156128 q = 1) (hb : d157647 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156128, d157647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156128, d157647, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156129 q = 1) (hb : d157648 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156129, d157648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156129, d157648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30607 (p : Pattern) (ha : d156131 p = 1) (hb : d157650 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156098 q = 1) (hb : d157617 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156098, d157617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156098, d157617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30560 q ha hb
  have h2 (q : Pattern) (ha : d155877 q = 1) (hb : d157403 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d155877, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30560 q ha hb
    | true =>
      simp only [d155877, d157403, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156099 q = 1) (hb : d157618 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156099, d157618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156099, d157618, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155878 q = 1) (hb : d157404 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d155878, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155878, d157404, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156100 q = 1) (hb : d157619 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156100, d157619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156100, d157619, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156101 q = 1) (hb : d157620 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156101, d157620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156101, d157620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156130 q = 1) (hb : d157649 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156130, d157649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156130, d157649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156131 q = 1) (hb : d157650 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156131, d157650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156131, d157650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30608 (p : Pattern) (ha : d156137 p = 1) (hb : d157656 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156132 q = 1) (hb : d157651 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156132, d157651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30602 q ha hb
    | true =>
      simp only [d156132, d157651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30607 q ha hb
  have h2 (q : Pattern) (ha : d156133 q = 1) (hb : d157652 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156133, d157652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156133, d157652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156134 q = 1) (hb : d157653 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156134, d157653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156134, d157653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156135 q = 1) (hb : d157654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156135, d157654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156135, d157654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156136 q = 1) (hb : d157655 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156136, d157655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156136, d157655, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156137 q = 1) (hb : d157656 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156137, d157656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156137, d157656, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30609 (p : Pattern) (ha : d156143 p = 1) (hb : d157662 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156124 q = 1) (hb : d157643 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156124, d157643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30605 q ha hb
    | true =>
      simp only [d156124, d157643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156125 q = 1) (hb : d157644 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156125, d157644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156125, d157644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156138 q = 1) (hb : d157657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156138, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30608 q ha hb
    | true =>
      simp only [d156138, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156139 q = 1) (hb : d157658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156139, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156139, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156140 q = 1) (hb : d157659 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156140, d157659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156140, d157659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156141 q = 1) (hb : d157660 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156141, d157660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156141, d157660, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156142 q = 1) (hb : d157661 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156142, d157661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156142, d157661, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156143 q = 1) (hb : d157662 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156143, d157662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156143, d157662, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30610 (p : Pattern) (ha : d156146 p = 1) (hb : d157666 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156104 q = 1) (hb : d157623 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156104, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30600 q ha hb
    | true =>
      simp only [d156104, d157623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30602 q ha hb
  have h2 (q : Pattern) (ha : d156105 q = 1) (hb : d157624 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156105, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156105, d157624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156106 q = 1) (hb : d157625 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156106, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156106, d157625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156113 q = 1) (hb : d157632 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156113, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30602 q ha hb
    | true =>
      simp only [d156113, d157632, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30603 q ha hb
  have h5 (q : Pattern) (ha : d156114 q = 1) (hb : d157633 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156114, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156114, d157633, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156115 q = 1) (hb : d157634 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156115, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156115, d157634, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156116 q = 1) (hb : d157635 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156116, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156116, d157635, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156132 q = 1) (hb : d157651 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156132, d157651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30602 q ha hb
    | true =>
      simp only [d156132, d157651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30607 q ha hb
  have h9 (q : Pattern) (ha : d156133 q = 1) (hb : d157652 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156133, d157652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156133, d157652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156134 q = 1) (hb : d157653 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156134, d157653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156134, d157653, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156135 q = 1) (hb : d157654 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156135, d157654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156135, d157654, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d156145 q = 1) (hb : d157665 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156145, d157665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156145, d157665, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156146 q = 1) (hb : d157666 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156146, d157666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d156146, d157666, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro30611 (p : Pattern) (ha : d156162 p = 1) (hb : d157672 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156147 q = 1) (hb : d157667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156147, d157667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30610 q ha hb
    | true =>
      simp only [d156147, d157667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156148 q = 1) (hb : d157668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156148, d157668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156148, d157668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156159 q = 1) (hb : d157669 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156159, d157669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156159, d157669, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156160 q = 1) (hb : d157670 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156160, d157670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156160, d157670, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156161 q = 1) (hb : d157671 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156161, d157671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156161, d157671, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156162 q = 1) (hb : d157672 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156162, d157672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156162, d157672, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30612 (p : Pattern) (ha : d156168 p = 1) (hb : d157678 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156144 q = 1) (hb : d157663 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156144, d157663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30606 q ha hb
    | true =>
      simp only [d156144, d157663, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30609 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156157 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156158 q = 1) (hb : d157664 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156158, d157664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156158, d157664, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d156163 q = 1) (hb : d157673 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156163, d157673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30611 q ha hb
    | true =>
      simp only [d156163, d157673, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156164 q = 1) (hb : d157674 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156164, d157674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156164, d157674, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156165 q = 1) (hb : d157675 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156165, d157675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156165, d157675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156166 q = 1) (hb : d157676 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156166, d157676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156166, d157676, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156167 q = 1) (hb : d157677 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156167, d157677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156167, d157677, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156168 q = 1) (hb : d157678 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156168, d157678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156168, d157678, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30613 (p : Pattern) (ha : d156156 p = 1) (hb : d157683 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156138 q = 1) (hb : d157657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156138, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30608 q ha hb
    | true =>
      simp only [d156138, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156139 q = 1) (hb : d157658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156139, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156139, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156153 q = 1) (hb : d157680 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156153, d157680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156153, d157680, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156154 q = 1) (hb : d157681 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156154, d157681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156154, d157681, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156155 q = 1) (hb : d157682 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156155, d157682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156155, d157682, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156156 q = 1) (hb : d157683 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156156, d157683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156156, d157683, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30614 (p : Pattern) (ha : d156175 p = 1) (hb : d157689 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156170 q = 1) (hb : d157684 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156170, d157684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30613 q ha hb
    | true =>
      simp only [d156170, d157684, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156171 q = 1) (hb : d157685 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156171, d157685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156171, d157685, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156172 q = 1) (hb : d157686 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156172, d157686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156172, d157686, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156173 q = 1) (hb : d157687 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156173, d157687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156173, d157687, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156174 q = 1) (hb : d157688 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156174, d157688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156174, d157688, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156175 q = 1) (hb : d157689 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156175, d157689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156175, d157689, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30615 (p : Pattern) (ha : d156181 p = 1) (hb : d157695 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155927 q = 1) (hb : d157451 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155927, d157451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155927, d157451, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30569 q ha hb
  have h2 (q : Pattern) (ha : d155928 q = 1) (hb : d157452 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155928, d157452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155928, d157452, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155937 q = 1) (hb : d157461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155937, d157461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30569 q ha hb
    | true =>
      simp only [d155937, d157461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30572 q ha hb
  have h4 (q : Pattern) (ha : d155938 q = 1) (hb : d157462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155938, d157462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155938, d157462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155939 q = 1) (hb : d157463 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155939, d157463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155939, d157463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156031 q = 1) (hb : d157556 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156031, d157556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30586 q ha hb
    | true =>
      simp only [d156031, d157556, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30594 q ha hb
  have h7 (q : Pattern) (ha : d156049 q = 1) (hb : d157574 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156049, d157574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30595 q ha hb
    | true =>
      simp only [d156049, d157574, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30596 q ha hb
  have h8 (q : Pattern) (ha : d156050 q = 1) (hb : d157575 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156050, d157575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156050, d157575, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156051 q = 1) (hb : d157576 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156051, d157576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156051, d157576, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d156052 q = 1) (hb : d157577 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156052, d157577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156052, d157577, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156056 q = 1) (hb : d157581 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156056, d157581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156056, d157581, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30597 q ha hb
  have h12 (q : Pattern) (ha : d156058 q = 1) (hb : d157583 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156058, d157583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156058, d157583, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30598 q ha hb
  have h13 (q : Pattern) (ha : d156059 q = 1) (hb : d157584 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156059, d157584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156059, d157584, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156060 q = 1) (hb : d157585 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156060, d157585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156060, d157585, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d156061 q = 1) (hb : d157586 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156061, d157586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d156061, d157586, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d156062 q = 1) (hb : d157587 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156062, d157587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156062, d157587, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156169 q = 1) (hb : d157679 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156169, d157679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156169, d157679, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30612 q ha hb
  have h18 (q : Pattern) (ha : d156176 q = 1) (hb : d157690 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156176, d157690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156176, d157690, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30614 q ha hb
  have h19 (q : Pattern) (ha : d156177 q = 1) (hb : d157691 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156177, d157691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d156177, d157691, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d156178 q = 1) (hb : d157692 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156178, d157692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d156178, d157692, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d156179 q = 1) (hb : d157693 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156179, d157693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d156179, d157693, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d156180 q = 1) (hb : d157694 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156180, d157694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d156180, d157694, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d156181 q = 1) (hb : d157695 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d156181, d157695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d156181, d157695, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30616 (p : Pattern) (ha : d156187 p = 1) (hb : d157701 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156182 q = 1) (hb : d157696 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d156182, d157696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156182, d157696, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30615 q ha hb
  have h2 (q : Pattern) (ha : d156183 q = 1) (hb : d157697 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d156183, d157697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156183, d157697, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156184 q = 1) (hb : d157698 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d156184, d157698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156184, d157698, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156185 q = 1) (hb : d157699 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d156185, d157699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156185, d157699, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156186 q = 1) (hb : d157700 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d156186, d157700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156186, d157700, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156187 q = 1) (hb : d157701 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d156187, d157701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156187, d157701, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30617 (p : Pattern) (ha : d27014 p = 1) (hb : d156193 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156193 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2004 q = 1) (hb : d53283 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro255 q ha hb
    | true =>
      simp only [d2004, d53283, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro256 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2008 q = 1) (hb : d53287 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2008, d53287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro257 q ha hb
  have h4 (q : Pattern) (ha : d2009 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2009, d53288, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d10349 q = 1) (hb : d53288 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d10349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d10350 q = 1) (hb : d156192 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d10350, d156192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d10350, d156192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d10351 q = 1) (hb : d156193 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d10351, d156193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d10351, d156193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d27014 q = 1) (hb : d156193 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d27014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30618 (p : Pattern) (ha : d156199 p = 1) (hb : d157706 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156199 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d2020 q = 1) (hb : d53299 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro258 q ha hb
    | true =>
      simp only [d2020, d53299, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro259 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d2024 q = 1) (hb : d53303 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2024, d53303, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro260 q ha hb
  have h4 (q : Pattern) (ha : d2025 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2025, d53304, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d5715 q = 1) (hb : d53304 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d5715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d2029 q = 1) (hb : d53308 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro261 q ha hb
    | true =>
      simp only [d2029, d53308, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h8 (q : Pattern) (ha : d2030 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2030, d53309, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d27032 q = 1) (hb : d53309 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d27032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27033 q = 1) (hb : d156198 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27033, d156198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d27033, d156198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d27034 q = 1) (hb : d156199 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27034, d156199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d27034, d156199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h13 (q : Pattern) (ha : d156199 q = 1) (hb : d157706 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157706, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
  exact h13 p ha hb
theorem andIntro30619 (p : Pattern) (ha : d156205 p = 1) (hb : d157712 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27015 q = 1) (hb : d156194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d156194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30617 q ha hb
    | true =>
      simp only [d27015, d156194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27016 q = 1) (hb : d156195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d156195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27016, d156195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27017 q = 1) (hb : d156196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27017, d156196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27017, d156196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27018 q = 1) (hb : d156197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27018, d156197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27018, d156197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d156200 q = 1) (hb : d157707 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156200, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30618 q ha hb
    | true =>
      simp only [d156200, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156201 q = 1) (hb : d157708 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156201, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156201, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156202 q = 1) (hb : d157709 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156202, d157709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156202, d157709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156203 q = 1) (hb : d157710 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156203, d157710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156203, d157710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156204 q = 1) (hb : d157711 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156204, d157711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d156204, d157711, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156205 q = 1) (hb : d157712 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156205, d157712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156205, d157712, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30620 (p : Pattern) (ha : d156207 p = 1) (hb : d157715 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156207 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d53318 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d2058 q = 1) (hb : d53320 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2058, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d2058, d53320, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro264 q ha hb
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d2043 q = 1) (hb : d53322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d2043, d53322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro265 q ha hb
  have h5 (q : Pattern) (ha : d2059 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2059, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d2059, d53323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d2076 q = 1) (hb : d53323 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d2076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h9 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d2061 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156206 q = 1) (hb : d157713 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d156206, d157713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d156206, d157713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  have h13 (q : Pattern) (ha : d156207 q = 1) (hb : d157714 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d156207, d157714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d156207, d157714, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d156207 q = 1) (hb : d157715 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157715, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  exact h14 p ha hb
theorem andIntro30621 (p : Pattern) (ha : d156213 p = 1) (hb : d157721 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156200 q = 1) (hb : d157707 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156200, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30618 q ha hb
    | true =>
      simp only [d156200, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156201 q = 1) (hb : d157708 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156201, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156201, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156202 q = 1) (hb : d157709 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156202, d157709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156202, d157709, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156203 q = 1) (hb : d157710 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156203, d157710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156203, d157710, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156208 q = 1) (hb : d157716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156208, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30620 q ha hb
    | true =>
      simp only [d156208, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156209 q = 1) (hb : d157717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156209, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156209, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156210 q = 1) (hb : d157718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156210, d157718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156210, d157718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156211 q = 1) (hb : d157719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156211, d157719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156211, d157719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156212 q = 1) (hb : d157720 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156212, d157720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156212, d157720, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156213 q = 1) (hb : d157721 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156213, d157721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156213, d157721, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30622 (p : Pattern) (ha : d156218 p = 1) (hb : d157725 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d156218 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d5238 q = 1) (hb : d69322 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d5238, d69322, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
  have h3 (q : Pattern) (ha : d5239 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d5239, d69323, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d27181 q = 1) (hb : d69323 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d27181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d2047 q = 1) (hb : d53326 q = 1) : d0 q = 1 := by
    cases bit : q 223 with
    | false =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro266 q ha hb
    | true =>
      simp only [d2047, d53326, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h7 (q : Pattern) (ha : d2048 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 204 with
    | false =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d2048, d53327, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d2061 q = 1) (hb : d53327 q = 1) : d0 q = 1 := by
    cases bit : q 202 with
    | false =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d2061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d27182 q = 1) (hb : d156217 q = 1) : d0 q = 1 := by
    cases bit : q 201 with
    | false =>
      simp only [d27182, d156217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27182, d156217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d27183 q = 1) (hb : d156218 q = 1) : d0 q = 1 := by
    cases bit : q 182 with
    | false =>
      simp only [d27183, d156218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d27183, d156218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h12 (q : Pattern) (ha : d156218 q = 1) (hb : d157725 q = 1) : d0 q = 1 := by
    cases bit : q 180 with
    | false =>
      simp only [d157725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d157725, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
  exact h12 p ha hb
theorem andIntro30623 (p : Pattern) (ha : d156224 p = 1) (hb : d157731 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156219 q = 1) (hb : d157726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156219, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30622 q ha hb
    | true =>
      simp only [d156219, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156220 q = 1) (hb : d157727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156220, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156220, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156221 q = 1) (hb : d157728 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156221, d157728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156221, d157728, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156222 q = 1) (hb : d157729 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156222, d157729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156222, d157729, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156223 q = 1) (hb : d157730 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156223, d157730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156223, d157730, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156224 q = 1) (hb : d157731 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156224, d157731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156224, d157731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30624 (p : Pattern) (ha : d156230 p = 1) (hb : d157737 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156208 q = 1) (hb : d157716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156208, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30620 q ha hb
    | true =>
      simp only [d156208, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156209 q = 1) (hb : d157717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156209, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156209, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156210 q = 1) (hb : d157718 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156210, d157718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156210, d157718, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156211 q = 1) (hb : d157719 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156211, d157719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156211, d157719, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156229 q = 1) (hb : d157736 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156229, d157736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156229, d157736, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156230 q = 1) (hb : d157737 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156230, d157737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156230, d157737, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30625 (p : Pattern) (ha : d156236 p = 1) (hb : d157743 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156214 q = 1) (hb : d157722 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156214, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30619 q ha hb
    | true =>
      simp only [d156214, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30621 q ha hb
  have h2 (q : Pattern) (ha : d156215 q = 1) (hb : d157723 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156215, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156215, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156216 q = 1) (hb : d157724 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156216, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156216, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156225 q = 1) (hb : d157732 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156225, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30621 q ha hb
    | true =>
      simp only [d156225, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30623 q ha hb
  have h5 (q : Pattern) (ha : d156226 q = 1) (hb : d157733 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156226, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156226, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156227 q = 1) (hb : d157734 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156227, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156227, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156228 q = 1) (hb : d157735 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156228, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156228, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156231 q = 1) (hb : d157738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156231, d157738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30621 q ha hb
    | true =>
      simp only [d156231, d157738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30624 q ha hb
  have h9 (q : Pattern) (ha : d156232 q = 1) (hb : d157739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156232, d157739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156232, d157739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156233 q = 1) (hb : d157740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156233, d157740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156233, d157740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156234 q = 1) (hb : d157741 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156234, d157741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156234, d157741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d156235 q = 1) (hb : d157742 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156235, d157742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156235, d157742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156236 q = 1) (hb : d157743 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156236, d157743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d156236, d157743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro30626 (p : Pattern) (ha : d156240 p = 1) (hb : d157747 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156231 q = 1) (hb : d157738 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156231, d157738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30621 q ha hb
    | true =>
      simp only [d156231, d157738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30624 q ha hb
  have h2 (q : Pattern) (ha : d156232 q = 1) (hb : d157739 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156232, d157739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156232, d157739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156233 q = 1) (hb : d157740 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156233, d157740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156233, d157740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156234 q = 1) (hb : d157741 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156234, d157741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156234, d157741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156239 q = 1) (hb : d157746 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156239, d157746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156239, d157746, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156240 q = 1) (hb : d157747 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156240, d157747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156240, d157747, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30627 (p : Pattern) (ha : d156246 p = 1) (hb : d157753 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156237 q = 1) (hb : d157744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30625 q ha hb
    | true =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156238 q = 1) (hb : d157745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156243 q = 1) (hb : d157750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156244 q = 1) (hb : d157751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156244, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156244, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156245 q = 1) (hb : d157752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156245, d157752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156245, d157752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156246 q = 1) (hb : d157753 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156246, d157753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156246, d157753, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30628 (p : Pattern) (ha : d156250 p = 1) (hb : d157757 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156247 q = 1) (hb : d157754 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156248 q = 1) (hb : d157755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156248, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156248, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156249 q = 1) (hb : d157756 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156249, d157756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156249, d157756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156250 q = 1) (hb : d157757 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156250, d157757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156250, d157757, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30629 (p : Pattern) (ha : d156256 p = 1) (hb : d157763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156251 q = 1) (hb : d157758 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156251, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30627 q ha hb
    | true =>
      simp only [d156251, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30628 q ha hb
  have h2 (q : Pattern) (ha : d156252 q = 1) (hb : d157759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156252, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156252, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156253 q = 1) (hb : d157760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156253, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156253, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156254 q = 1) (hb : d157761 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156254, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156254, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156255 q = 1) (hb : d157762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156255, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156255, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156256 q = 1) (hb : d157763 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156256, d157763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156256, d157763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30630 (p : Pattern) (ha : d156259 p = 1) (hb : d157766 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156237 q = 1) (hb : d157744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30625 q ha hb
    | true =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156238 q = 1) (hb : d157745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156243 q = 1) (hb : d157750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156244 q = 1) (hb : d157751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156244, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156244, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156245 q = 1) (hb : d157752 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156245, d157752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156245, d157752, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156259 q = 1) (hb : d157766 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156259, d157766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156259, d157766, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30631 (p : Pattern) (ha : d156260 p = 1) (hb : d157767 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156247 q = 1) (hb : d157754 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156248 q = 1) (hb : d157755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156248, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156248, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156249 q = 1) (hb : d157756 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156249, d157756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156249, d157756, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156260 q = 1) (hb : d157767 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156260, d157767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156260, d157767, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30632 (p : Pattern) (ha : d156266 p = 1) (hb : d157773 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156251 q = 1) (hb : d157758 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156251, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30627 q ha hb
    | true =>
      simp only [d156251, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30628 q ha hb
  have h2 (q : Pattern) (ha : d156252 q = 1) (hb : d157759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156252, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156252, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156253 q = 1) (hb : d157760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156253, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156253, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156254 q = 1) (hb : d157761 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156254, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156254, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156255 q = 1) (hb : d157762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156255, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156255, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156261 q = 1) (hb : d157768 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156261, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30630 q ha hb
    | true =>
      simp only [d156261, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30631 q ha hb
  have h7 (q : Pattern) (ha : d156262 q = 1) (hb : d157769 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156262, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156262, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156263 q = 1) (hb : d157770 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156263, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156263, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156264 q = 1) (hb : d157771 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156264, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156264, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156265 q = 1) (hb : d157772 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156265, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156265, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156266 q = 1) (hb : d157773 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156266, d157773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156266, d157773, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30633 (p : Pattern) (ha : d156271 p = 1) (hb : d157778 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156237 q = 1) (hb : d157744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30625 q ha hb
    | true =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156238 q = 1) (hb : d157745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156243 q = 1) (hb : d157750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156244 q = 1) (hb : d157751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156244, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156244, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156270 q = 1) (hb : d157777 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156270, d157777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156270, d157777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156271 q = 1) (hb : d157778 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156271, d157778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156271, d157778, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30634 (p : Pattern) (ha : d156273 p = 1) (hb : d157780 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156247 q = 1) (hb : d157754 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156248 q = 1) (hb : d157755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156248, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156248, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156272 q = 1) (hb : d157779 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156272, d157779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156272, d157779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156273 q = 1) (hb : d157780 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156273, d157780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156273, d157780, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30635 (p : Pattern) (ha : d156280 p = 1) (hb : d157787 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156237 q = 1) (hb : d157744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30625 q ha hb
    | true =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156238 q = 1) (hb : d157745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156243 q = 1) (hb : d157750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156278 q = 1) (hb : d157785 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156278, d157785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156278, d157785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156279 q = 1) (hb : d157786 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156279, d157786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156279, d157786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156280 q = 1) (hb : d157787 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156280, d157787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156280, d157787, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30636 (p : Pattern) (ha : d156283 p = 1) (hb : d157790 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156247 q = 1) (hb : d157754 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156281 q = 1) (hb : d157788 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156281, d157788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156281, d157788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156282 q = 1) (hb : d157789 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156282, d157789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156282, d157789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156283 q = 1) (hb : d157790 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156283, d157790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156283, d157790, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30637 (p : Pattern) (ha : d156288 p = 1) (hb : d157794 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27015 q = 1) (hb : d156194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d156194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30617 q ha hb
    | true =>
      simp only [d27015, d156194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d27016 q = 1) (hb : d156195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d156195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27016, d156195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27017 q = 1) (hb : d156196 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27017, d156196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27017, d156196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27018 q = 1) (hb : d156197 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27018, d156197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27018, d156197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27105 q = 1) (hb : d156287 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27105, d156287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27105, d156287, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156288 q = 1) (hb : d157794 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156288, d157794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
    | true =>
      simp only [d156288, d157794, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30638 (p : Pattern) (ha : d156297 p = 1) (hb : d157803 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156289 q = 1) (hb : d157795 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156289, d157795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30637 q ha hb
    | true =>
      simp only [d156289, d157795, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30619 q ha hb
  have h2 (q : Pattern) (ha : d156290 q = 1) (hb : d157796 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156290, d157796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156290, d157796, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156291 q = 1) (hb : d157797 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156291, d157797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156291, d157797, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156292 q = 1) (hb : d157798 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156292, d157798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30619 q ha hb
    | true =>
      simp only [d156292, d157798, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156293 q = 1) (hb : d157799 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156293, d157799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156293, d157799, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156294 q = 1) (hb : d157800 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156294, d157800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156294, d157800, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156295 q = 1) (hb : d157801 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156295, d157801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156295, d157801, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156214 q = 1) (hb : d157722 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156214, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30619 q ha hb
    | true =>
      simp only [d156214, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30621 q ha hb
  have h9 (q : Pattern) (ha : d156215 q = 1) (hb : d157723 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156215, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156215, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156216 q = 1) (hb : d157724 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156216, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156216, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156225 q = 1) (hb : d157732 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156225, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30621 q ha hb
    | true =>
      simp only [d156225, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30623 q ha hb
  have h12 (q : Pattern) (ha : d156226 q = 1) (hb : d157733 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156226, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156226, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156227 q = 1) (hb : d157734 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156227, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156227, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156228 q = 1) (hb : d157735 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156228, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156228, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156296 q = 1) (hb : d157802 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156296, d157802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156296, d157802, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156297 q = 1) (hb : d157803 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156297, d157803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156297, d157803, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro30639 (p : Pattern) (ha : d156302 p = 1) (hb : d157808 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156214 q = 1) (hb : d157722 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156214, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30619 q ha hb
    | true =>
      simp only [d156214, d157722, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30621 q ha hb
  have h2 (q : Pattern) (ha : d156215 q = 1) (hb : d157723 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156215, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156215, d157723, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156216 q = 1) (hb : d157724 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156216, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156216, d157724, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156225 q = 1) (hb : d157732 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156225, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30621 q ha hb
    | true =>
      simp only [d156225, d157732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30623 q ha hb
  have h5 (q : Pattern) (ha : d156226 q = 1) (hb : d157733 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156226, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156226, d157733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156227 q = 1) (hb : d157734 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156227, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156227, d157734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156228 q = 1) (hb : d157735 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156228, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156228, d157735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156300 q = 1) (hb : d157806 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156300, d157806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156300, d157806, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156301 q = 1) (hb : d157807 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156301, d157807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156301, d157807, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156302 q = 1) (hb : d157808 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156302, d157808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156302, d157808, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30640 (p : Pattern) (ha : d156308 p = 1) (hb : d157814 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156298 q = 1) (hb : d157804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156298, d157804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30638 q ha hb
    | true =>
      simp only [d156298, d157804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156299 q = 1) (hb : d157805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156299, d157805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156299, d157805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156303 q = 1) (hb : d157809 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156303, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30639 q ha hb
    | true =>
      simp only [d156303, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156304 q = 1) (hb : d157810 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156304, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156304, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156305 q = 1) (hb : d157811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156305, d157811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156305, d157811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156306 q = 1) (hb : d157812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156306, d157812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156306, d157812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156307 q = 1) (hb : d157813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156307, d157813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156307, d157813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156308 q = 1) (hb : d157814 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156308, d157814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156308, d157814, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30641 (p : Pattern) (ha : d156312 p = 1) (hb : d157818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156303 q = 1) (hb : d157809 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156303, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30639 q ha hb
    | true =>
      simp only [d156303, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156304 q = 1) (hb : d157810 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156304, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156304, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156309 q = 1) (hb : d157815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156309, d157815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156309, d157815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156310 q = 1) (hb : d157816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156310, d157816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156310, d157816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156311 q = 1) (hb : d157817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156311, d157817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156311, d157817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156312 q = 1) (hb : d157818 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156312, d157818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156312, d157818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30642 (p : Pattern) (ha : d156318 p = 1) (hb : d157824 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156237 q = 1) (hb : d157744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30625 q ha hb
    | true =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156238 q = 1) (hb : d157745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156315 q = 1) (hb : d157821 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156315, d157821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156315, d157821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156316 q = 1) (hb : d157822 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156316, d157822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156316, d157822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156317 q = 1) (hb : d157823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156317, d157823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156317, d157823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156318 q = 1) (hb : d157824 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156318, d157824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156318, d157824, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30643 (p : Pattern) (ha : d156324 p = 1) (hb : d157830 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156274 q = 1) (hb : d157781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156274, d157781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30633 q ha hb
    | true =>
      simp only [d156274, d157781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30634 q ha hb
  have h2 (q : Pattern) (ha : d156275 q = 1) (hb : d157782 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156275, d157782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156275, d157782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156276 q = 1) (hb : d157783 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156276, d157783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156276, d157783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156277 q = 1) (hb : d157784 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156277, d157784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156277, d157784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156284 q = 1) (hb : d157791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156284, d157791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30635 q ha hb
    | true =>
      simp only [d156284, d157791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30636 q ha hb
  have h6 (q : Pattern) (ha : d156285 q = 1) (hb : d157792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156285, d157792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156285, d157792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156286 q = 1) (hb : d157793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156286, d157793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156286, d157793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156313 q = 1) (hb : d157819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156313, d157819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30640 q ha hb
    | true =>
      simp only [d156313, d157819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30641 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d156251 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d156314 q = 1) (hb : d157820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156314, d157820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156314, d157820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d156319 q = 1) (hb : d157825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156319, d157825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30642 q ha hb
    | true =>
      simp only [d156319, d157825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d156320 q = 1) (hb : d157826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156320, d157826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156320, d157826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156321 q = 1) (hb : d157827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156321, d157827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156321, d157827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156322 q = 1) (hb : d157828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156322, d157828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156322, d157828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156323 q = 1) (hb : d157829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156323, d157829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156323, d157829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156324 q = 1) (hb : d157830 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156324, d157830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156324, d157830, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  exact h16 p ha hb
theorem andIntro30644 (p : Pattern) (ha : d156325 p = 1) (hb : d157831 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156237 q = 1) (hb : d157744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30625 q ha hb
    | true =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156238 q = 1) (hb : d157745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156243 q = 1) (hb : d157750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156244 q = 1) (hb : d157751 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156244, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156244, d157751, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156270 q = 1) (hb : d157777 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156270, d157777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156270, d157777, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156325 q = 1) (hb : d157831 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156325, d157831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156325, d157831, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30645 (p : Pattern) (ha : d156326 p = 1) (hb : d157832 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156247 q = 1) (hb : d157754 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156248 q = 1) (hb : d157755 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156248, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156248, d157755, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156272 q = 1) (hb : d157779 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156272, d157779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156272, d157779, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156326 q = 1) (hb : d157832 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156326, d157832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156326, d157832, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30646 (p : Pattern) (ha : d156331 p = 1) (hb : d157837 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156237 q = 1) (hb : d157744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30625 q ha hb
    | true =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156238 q = 1) (hb : d157745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156243 q = 1) (hb : d157750 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156243, d157750, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156278 q = 1) (hb : d157785 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156278, d157785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156278, d157785, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156279 q = 1) (hb : d157786 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156279, d157786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156279, d157786, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156331 q = 1) (hb : d157837 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156331, d157837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156331, d157837, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30647 (p : Pattern) (ha : d156332 p = 1) (hb : d157838 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156247 q = 1) (hb : d157754 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156247, d157754, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156281 q = 1) (hb : d157788 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156281, d157788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156281, d157788, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156282 q = 1) (hb : d157789 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156282, d157789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156282, d157789, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156332 q = 1) (hb : d157838 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156332, d157838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156332, d157838, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30648 (p : Pattern) (ha : d156336 p = 1) (hb : d157842 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156298 q = 1) (hb : d157804 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156298, d157804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30638 q ha hb
    | true =>
      simp only [d156298, d157804, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156299 q = 1) (hb : d157805 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156299, d157805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156299, d157805, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156303 q = 1) (hb : d157809 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156303, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30639 q ha hb
    | true =>
      simp only [d156303, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156304 q = 1) (hb : d157810 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156304, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156304, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156305 q = 1) (hb : d157811 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156305, d157811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156305, d157811, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156306 q = 1) (hb : d157812 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156306, d157812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156306, d157812, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156307 q = 1) (hb : d157813 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156307, d157813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156307, d157813, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156336 q = 1) (hb : d157842 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156336, d157842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156336, d157842, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30649 (p : Pattern) (ha : d156337 p = 1) (hb : d157843 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156303 q = 1) (hb : d157809 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156303, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30639 q ha hb
    | true =>
      simp only [d156303, d157809, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156304 q = 1) (hb : d157810 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156304, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156304, d157810, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156241 q = 1) (hb : d157748 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30626 q ha hb
    | true =>
      simp only [d156241, d157748, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156242 q = 1) (hb : d157749 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156242, d157749, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156309 q = 1) (hb : d157815 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156309, d157815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156309, d157815, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156310 q = 1) (hb : d157816 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156310, d157816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156310, d157816, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156311 q = 1) (hb : d157817 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156311, d157817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156311, d157817, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156337 q = 1) (hb : d157843 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156337, d157843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156337, d157843, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30650 (p : Pattern) (ha : d156340 p = 1) (hb : d157846 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156237 q = 1) (hb : d157744 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30625 q ha hb
    | true =>
      simp only [d156237, d157744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156238 q = 1) (hb : d157745 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156238, d157745, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156315 q = 1) (hb : d157821 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156315, d157821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156315, d157821, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156316 q = 1) (hb : d157822 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156316, d157822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156316, d157822, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156317 q = 1) (hb : d157823 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156317, d157823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156317, d157823, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156340 q = 1) (hb : d157846 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156340, d157846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156340, d157846, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30651 (p : Pattern) (ha : d156346 p = 1) (hb : d157852 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156274 q = 1) (hb : d157781 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156274, d157781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30633 q ha hb
    | true =>
      simp only [d156274, d157781, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30634 q ha hb
  have h2 (q : Pattern) (ha : d156275 q = 1) (hb : d157782 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156275, d157782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156275, d157782, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156276 q = 1) (hb : d157783 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156276, d157783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156276, d157783, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156277 q = 1) (hb : d157784 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156277, d157784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156277, d157784, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156284 q = 1) (hb : d157791 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156284, d157791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30635 q ha hb
    | true =>
      simp only [d156284, d157791, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30636 q ha hb
  have h6 (q : Pattern) (ha : d156285 q = 1) (hb : d157792 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156285, d157792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156285, d157792, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156286 q = 1) (hb : d157793 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156286, d157793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156286, d157793, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156313 q = 1) (hb : d157819 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156313, d157819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30640 q ha hb
    | true =>
      simp only [d156313, d157819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30641 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d156251 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d156314 q = 1) (hb : d157820 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156314, d157820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156314, d157820, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
  have h11 (q : Pattern) (ha : d156319 q = 1) (hb : d157825 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156319, d157825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30642 q ha hb
    | true =>
      simp only [d156319, d157825, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d156320 q = 1) (hb : d157826 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156320, d157826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156320, d157826, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156321 q = 1) (hb : d157827 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156321, d157827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156321, d157827, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156322 q = 1) (hb : d157828 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156322, d157828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156322, d157828, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156323 q = 1) (hb : d157829 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156323, d157829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156323, d157829, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156327 q = 1) (hb : d157833 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156327, d157833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30644 q ha hb
    | true =>
      simp only [d156327, d157833, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30645 q ha hb
  have h17 (q : Pattern) (ha : d156328 q = 1) (hb : d157834 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156328, d157834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156328, d157834, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156329 q = 1) (hb : d157835 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156329, d157835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d156329, d157835, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h19 (q : Pattern) (ha : d156330 q = 1) (hb : d157836 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156330, d157836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156330, d157836, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d156333 q = 1) (hb : d157839 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156333, d157839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30646 q ha hb
    | true =>
      simp only [d156333, d157839, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30647 q ha hb
  have h21 (q : Pattern) (ha : d156334 q = 1) (hb : d157840 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156334, d157840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156334, d157840, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
  have h22 (q : Pattern) (ha : d156335 q = 1) (hb : d157841 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156335, d157841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d156335, d157841, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d156338 q = 1) (hb : d157844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156338, d157844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30648 q ha hb
    | true =>
      simp only [d156338, d157844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30649 q ha hb
  have h24 (q : Pattern) (ha : d0 q = 1) (hb : d156261 q = 1) : d0 q = 1 := by
    exact ha
  have h25 (q : Pattern) (ha : d156339 q = 1) (hb : d157845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156339, d157845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h23 q ha hb
    | true =>
      simp only [d156339, d157845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h24 q hb ha
  have h26 (q : Pattern) (ha : d156341 q = 1) (hb : d157847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156341, d157847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30650 q ha hb
    | true =>
      simp only [d156341, d157847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h27 (q : Pattern) (ha : d156342 q = 1) (hb : d157848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156342, d157848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h26 q ha hb
    | true =>
      simp only [d156342, d157848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h28 (q : Pattern) (ha : d156343 q = 1) (hb : d157849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156343, d157849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h25 q ha hb
    | true =>
      simp only [d156343, d157849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h27 q ha hb
  have h29 (q : Pattern) (ha : d156344 q = 1) (hb : d157850 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156344, d157850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
    | true =>
      simp only [d156344, d157850, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h28 q ha hb
  have h30 (q : Pattern) (ha : d156345 q = 1) (hb : d157851 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156345, d157851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d156345, d157851, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h29 q ha hb
  have h31 (q : Pattern) (ha : d156346 q = 1) (hb : d157852 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156346, d157852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156346, d157852, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h30 q ha hb
  exact h31 p ha hb
theorem andIntro30652 (p : Pattern) (ha : d156358 p = 1) (hb : d157864 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156348 q = 1) (hb : d157854 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156348, d157854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30641 q ha hb
    | true =>
      simp only [d156348, d157854, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30628 q ha hb
  have h2 (q : Pattern) (ha : d156349 q = 1) (hb : d157855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156349, d157855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156349, d157855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156350 q = 1) (hb : d157856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156350, d157856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156350, d157856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156351 q = 1) (hb : d157857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156351, d157857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156351, d157857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156352 q = 1) (hb : d157858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156352, d157858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156352, d157858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156353 q = 1) (hb : d157859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156353, d157859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30628 q ha hb
    | true =>
      simp only [d156353, d157859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156354 q = 1) (hb : d157860 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156354, d157860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156354, d157860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156355 q = 1) (hb : d157861 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156355, d157861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156355, d157861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156356 q = 1) (hb : d157862 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156356, d157862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156356, d157862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156357 q = 1) (hb : d157863 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156357, d157863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156357, d157863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156358 q = 1) (hb : d157864 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156358, d157864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156358, d157864, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30653 (p : Pattern) (ha : d156364 p = 1) (hb : d157870 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156353 q = 1) (hb : d157859 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156353, d157859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30628 q ha hb
    | true =>
      simp only [d156353, d157859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156354 q = 1) (hb : d157860 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156354, d157860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156354, d157860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156355 q = 1) (hb : d157861 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156355, d157861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156355, d157861, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156356 q = 1) (hb : d157862 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156356, d157862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156356, d157862, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156357 q = 1) (hb : d157863 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156357, d157863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156357, d157863, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156359 q = 1) (hb : d157865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156359, d157865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30631 q ha hb
    | true =>
      simp only [d156359, d157865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156360 q = 1) (hb : d157866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156360, d157866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156360, d157866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156361 q = 1) (hb : d157867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156361, d157867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156361, d157867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156362 q = 1) (hb : d157868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156362, d157868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156362, d157868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156363 q = 1) (hb : d157869 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156363, d157869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156363, d157869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156364 q = 1) (hb : d157870 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156364, d157870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156364, d157870, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30654 (p : Pattern) (ha : d156371 p = 1) (hb : d157877 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156338 q = 1) (hb : d157844 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156338, d157844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30648 q ha hb
    | true =>
      simp only [d156338, d157844, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30649 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156261 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156339 q = 1) (hb : d157845 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156339, d157845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156339, d157845, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d156341 q = 1) (hb : d157847 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156341, d157847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30650 q ha hb
    | true =>
      simp only [d156341, d157847, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156342 q = 1) (hb : d157848 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156342, d157848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156342, d157848, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156343 q = 1) (hb : d157849 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156343, d157849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156343, d157849, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156369 q = 1) (hb : d157875 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156369, d157875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156369, d157875, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156370 q = 1) (hb : d157876 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156370, d157876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156370, d157876, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156371 q = 1) (hb : d157877 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156371, d157877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156371, d157877, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30655 (p : Pattern) (ha : d156373 p = 1) (hb : d157879 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156359 q = 1) (hb : d157865 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156359, d157865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30631 q ha hb
    | true =>
      simp only [d156359, d157865, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156360 q = 1) (hb : d157866 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156360, d157866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156360, d157866, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156361 q = 1) (hb : d157867 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156361, d157867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156361, d157867, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156362 q = 1) (hb : d157868 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156362, d157868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156362, d157868, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156363 q = 1) (hb : d157869 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156363, d157869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156363, d157869, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156373 q = 1) (hb : d157879 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156373, d157879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156373, d157879, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30656 (p : Pattern) (ha : d156384 p = 1) (hb : d157885 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27267 q = 1) (hb : d156379 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27267, d156379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27267, d156379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30617 q ha hb
  have h2 (q : Pattern) (ha : d27015 q = 1) (hb : d156194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d156194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30617 q ha hb
    | true =>
      simp only [d27015, d156194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27268 q = 1) (hb : d156380 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27268, d156380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27268, d156380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27016 q = 1) (hb : d156195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d156195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27016, d156195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27269 q = 1) (hb : d156381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27269, d156381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27269, d156381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27270 q = 1) (hb : d156382 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27270, d156382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27270, d156382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d27271 q = 1) (hb : d156383 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d27271, d156383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27271, d156383, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156384 q = 1) (hb : d157885 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156384, d157885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q hb ha
    | true =>
      simp only [d156384, d157885, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30657 (p : Pattern) (ha : d156390 p = 1) (hb : d157891 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d27267 q = 1) (hb : d156379 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27267, d156379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d27267, d156379, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30617 q ha hb
  have h2 (q : Pattern) (ha : d27015 q = 1) (hb : d156194 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d27015, d156194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30617 q ha hb
    | true =>
      simp only [d27015, d156194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d27268 q = 1) (hb : d156380 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27268, d156380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d27268, d156380, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d27016 q = 1) (hb : d156195 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d27016, d156195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d27016, d156195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d27269 q = 1) (hb : d156381 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d27269, d156381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d27269, d156381, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d27270 q = 1) (hb : d156382 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d27270, d156382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d27270, d156382, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d156385 q = 1) (hb : d157886 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156385, d157886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156385, d157886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30618 q ha hb
  have h8 (q : Pattern) (ha : d156200 q = 1) (hb : d157707 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156200, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30618 q ha hb
    | true =>
      simp only [d156200, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156386 q = 1) (hb : d157887 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156386, d157887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156386, d157887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156201 q = 1) (hb : d157708 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156201, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156201, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d156387 q = 1) (hb : d157888 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156387, d157888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156387, d157888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156388 q = 1) (hb : d157889 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156388, d157889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156388, d157889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156389 q = 1) (hb : d157890 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156389, d157890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
    | true =>
      simp only [d156389, d157890, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156390 q = 1) (hb : d157891 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156390, d157891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156390, d157891, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro30658 (p : Pattern) (ha : d156403 p = 1) (hb : d157904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156385 q = 1) (hb : d157886 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156385, d157886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156385, d157886, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30618 q ha hb
  have h2 (q : Pattern) (ha : d156200 q = 1) (hb : d157707 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156200, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30618 q ha hb
    | true =>
      simp only [d156200, d157707, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156386 q = 1) (hb : d157887 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156386, d157887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156386, d157887, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156201 q = 1) (hb : d157708 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156201, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156201, d157708, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156387 q = 1) (hb : d157888 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156387, d157888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156387, d157888, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156388 q = 1) (hb : d157889 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156388, d157889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156388, d157889, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156398 q = 1) (hb : d157899 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156398, d157899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156398, d157899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30620 q ha hb
  have h8 (q : Pattern) (ha : d156208 q = 1) (hb : d157716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156208, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30620 q ha hb
    | true =>
      simp only [d156208, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156399 q = 1) (hb : d157900 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156399, d157900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156399, d157900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156209 q = 1) (hb : d157717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156209, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156209, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h11 (q : Pattern) (ha : d156400 q = 1) (hb : d157901 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156400, d157901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156400, d157901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d156401 q = 1) (hb : d157902 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156401, d157902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156401, d157902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h13 (q : Pattern) (ha : d156402 q = 1) (hb : d157903 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156402, d157903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156402, d157903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156403 q = 1) (hb : d157904 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156403, d157904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156403, d157904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h14 p ha hb
theorem andIntro30659 (p : Pattern) (ha : d156412 p = 1) (hb : d157913 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156407 q = 1) (hb : d157908 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156407, d157908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156407, d157908, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30622 q ha hb
  have h2 (q : Pattern) (ha : d156219 q = 1) (hb : d157726 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156219, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30622 q ha hb
    | true =>
      simp only [d156219, d157726, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156408 q = 1) (hb : d157909 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156408, d157909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156408, d157909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156220 q = 1) (hb : d157727 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156220, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156220, d157727, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156409 q = 1) (hb : d157910 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156409, d157910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156409, d157910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156410 q = 1) (hb : d157911 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156410, d157911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156410, d157911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156411 q = 1) (hb : d157912 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156411, d157912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156411, d157912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156412 q = 1) (hb : d157913 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156412, d157913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156412, d157913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30660 (p : Pattern) (ha : d156418 p = 1) (hb : d157919 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156391 q = 1) (hb : d157892 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156391, d157892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30656 q ha hb
    | true =>
      simp only [d156391, d157892, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30657 q ha hb
  have h2 (q : Pattern) (ha : d156392 q = 1) (hb : d157893 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156392, d157893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156392, d157893, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156393 q = 1) (hb : d157894 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156393, d157894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156393, d157894, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156394 q = 1) (hb : d157895 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156394, d157895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30657 q ha hb
    | true =>
      simp only [d156394, d157895, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156395 q = 1) (hb : d157896 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156395, d157896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156395, d157896, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156396 q = 1) (hb : d157897 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156396, d157897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156396, d157897, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156397 q = 1) (hb : d157898 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156397, d157898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156397, d157898, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156404 q = 1) (hb : d157905 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156404, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30657 q ha hb
    | true =>
      simp only [d156404, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30658 q ha hb
  have h9 (q : Pattern) (ha : d156405 q = 1) (hb : d157906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156405, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156405, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156406 q = 1) (hb : d157907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156406, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156406, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156413 q = 1) (hb : d157914 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156413, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30658 q ha hb
    | true =>
      simp only [d156413, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30659 q ha hb
  have h12 (q : Pattern) (ha : d156414 q = 1) (hb : d157915 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156414, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156414, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156415 q = 1) (hb : d157916 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156415, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156415, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156416 q = 1) (hb : d157917 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156416, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156416, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156417 q = 1) (hb : d157918 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156417, d157918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156417, d157918, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156418 q = 1) (hb : d157919 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156418, d157919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156418, d157919, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h16 p ha hb
theorem andIntro30661 (p : Pattern) (ha : d156423 p = 1) (hb : d157924 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156404 q = 1) (hb : d157905 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156404, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30657 q ha hb
    | true =>
      simp only [d156404, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30658 q ha hb
  have h2 (q : Pattern) (ha : d156405 q = 1) (hb : d157906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156405, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156405, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156406 q = 1) (hb : d157907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156406, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156406, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156413 q = 1) (hb : d157914 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156413, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30658 q ha hb
    | true =>
      simp only [d156413, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30659 q ha hb
  have h5 (q : Pattern) (ha : d156414 q = 1) (hb : d157915 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156414, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156414, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156415 q = 1) (hb : d157916 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156415, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156415, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156416 q = 1) (hb : d157917 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156416, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156416, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156421 q = 1) (hb : d157922 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156421, d157922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156421, d157922, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h9 (q : Pattern) (ha : d156422 q = 1) (hb : d157923 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156422, d157923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156422, d157923, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156423 q = 1) (hb : d157924 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156423, d157924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156423, d157924, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h10 p ha hb
theorem andIntro30662 (p : Pattern) (ha : d156429 p = 1) (hb : d157930 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156419 q = 1) (hb : d157920 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156419, d157920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30660 q ha hb
    | true =>
      simp only [d156419, d157920, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156420 q = 1) (hb : d157921 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156420, d157921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156420, d157921, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156424 q = 1) (hb : d157925 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156424, d157925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30661 q ha hb
    | true =>
      simp only [d156424, d157925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156425 q = 1) (hb : d157926 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156425, d157926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156425, d157926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156426 q = 1) (hb : d157927 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156426, d157927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156426, d157927, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156427 q = 1) (hb : d157928 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156427, d157928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156427, d157928, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156428 q = 1) (hb : d157929 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156428, d157929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156428, d157929, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156429 q = 1) (hb : d157930 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156429, d157930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156429, d157930, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30663 (p : Pattern) (ha : d156431 p = 1) (hb : d157932 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156398 q = 1) (hb : d157899 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156398, d157899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156398, d157899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30620 q ha hb
  have h2 (q : Pattern) (ha : d156208 q = 1) (hb : d157716 q = 1) : d0 q = 1 := by
    cases bit : q 163 with
    | false =>
      simp only [d156208, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30620 q ha hb
    | true =>
      simp only [d156208, d157716, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156399 q = 1) (hb : d157900 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156399, d157900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156399, d157900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156209 q = 1) (hb : d157717 q = 1) : d0 q = 1 := by
    cases bit : q 162 with
    | false =>
      simp only [d156209, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156209, d157717, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156400 q = 1) (hb : d157901 q = 1) : d0 q = 1 := by
    cases bit : q 161 with
    | false =>
      simp only [d156400, d157901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156400, d157901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156401 q = 1) (hb : d157902 q = 1) : d0 q = 1 := by
    cases bit : q 160 with
    | false =>
      simp only [d156401, d157902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156401, d157902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156430 q = 1) (hb : d157931 q = 1) : d0 q = 1 := by
    cases bit : q 159 with
    | false =>
      simp only [d156430, d157931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156430, d157931, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156431 q = 1) (hb : d157932 q = 1) : d0 q = 1 := by
    cases bit : q 158 with
    | false =>
      simp only [d156431, d157932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156431, d157932, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30664 (p : Pattern) (ha : d156437 p = 1) (hb : d157938 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156432 q = 1) (hb : d157933 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156432, d157933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30658 q ha hb
    | true =>
      simp only [d156432, d157933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30663 q ha hb
  have h2 (q : Pattern) (ha : d156433 q = 1) (hb : d157934 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156433, d157934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156433, d157934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156434 q = 1) (hb : d157935 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156434, d157935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156434, d157935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156435 q = 1) (hb : d157936 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156435, d157936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156435, d157936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156436 q = 1) (hb : d157937 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156436, d157937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156436, d157937, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156437 q = 1) (hb : d157938 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156437, d157938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156437, d157938, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30665 (p : Pattern) (ha : d156443 p = 1) (hb : d157944 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156424 q = 1) (hb : d157925 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156424, d157925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30661 q ha hb
    | true =>
      simp only [d156424, d157925, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156425 q = 1) (hb : d157926 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156425, d157926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156425, d157926, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156438 q = 1) (hb : d157939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156438, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30664 q ha hb
    | true =>
      simp only [d156438, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156439 q = 1) (hb : d157940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156439, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156439, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156440 q = 1) (hb : d157941 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156440, d157941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156440, d157941, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156441 q = 1) (hb : d157942 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156441, d157942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156441, d157942, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156442 q = 1) (hb : d157943 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156442, d157943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156442, d157943, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156443 q = 1) (hb : d157944 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156443, d157944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156443, d157944, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30666 (p : Pattern) (ha : d156446 p = 1) (hb : d157948 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156404 q = 1) (hb : d157905 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156404, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30657 q ha hb
    | true =>
      simp only [d156404, d157905, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30658 q ha hb
  have h2 (q : Pattern) (ha : d156405 q = 1) (hb : d157906 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156405, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156405, d157906, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156406 q = 1) (hb : d157907 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156406, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156406, d157907, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156413 q = 1) (hb : d157914 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156413, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30658 q ha hb
    | true =>
      simp only [d156413, d157914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30659 q ha hb
  have h5 (q : Pattern) (ha : d156414 q = 1) (hb : d157915 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156414, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156414, d157915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156415 q = 1) (hb : d157916 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156415, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156415, d157916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156416 q = 1) (hb : d157917 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156416, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156416, d157917, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156432 q = 1) (hb : d157933 q = 1) : d0 q = 1 := by
    cases bit : q 157 with
    | false =>
      simp only [d156432, d157933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30658 q ha hb
    | true =>
      simp only [d156432, d157933, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30663 q ha hb
  have h9 (q : Pattern) (ha : d156433 q = 1) (hb : d157934 q = 1) : d0 q = 1 := by
    cases bit : q 141 with
    | false =>
      simp only [d156433, d157934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156433, d157934, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156434 q = 1) (hb : d157935 q = 1) : d0 q = 1 := by
    cases bit : q 138 with
    | false =>
      simp only [d156434, d157935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156434, d157935, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156435 q = 1) (hb : d157936 q = 1) : d0 q = 1 := by
    cases bit : q 136 with
    | false =>
      simp only [d156435, d157936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156435, d157936, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h12 (q : Pattern) (ha : d156445 q = 1) (hb : d157947 q = 1) : d0 q = 1 := by
    cases bit : q 135 with
    | false =>
      simp only [d156445, d157947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156445, d157947, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156446 q = 1) (hb : d157948 q = 1) : d0 q = 1 := by
    cases bit : q 119 with
    | false =>
      simp only [d156446, d157948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d156446, d157948, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h13 p ha hb
theorem andIntro30667 (p : Pattern) (ha : d156462 p = 1) (hb : d157954 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156447 q = 1) (hb : d157949 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156447, d157949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30666 q ha hb
    | true =>
      simp only [d156447, d157949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156448 q = 1) (hb : d157950 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156448, d157950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156448, d157950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156459 q = 1) (hb : d157951 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156459, d157951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156459, d157951, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156460 q = 1) (hb : d157952 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156460, d157952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156460, d157952, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156461 q = 1) (hb : d157953 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156461, d157953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156461, d157953, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156462 q = 1) (hb : d157954 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156462, d157954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156462, d157954, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30668 (p : Pattern) (ha : d156468 p = 1) (hb : d157960 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156444 q = 1) (hb : d157945 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156444, d157945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30662 q ha hb
    | true =>
      simp only [d156444, d157945, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30665 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156457 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156458 q = 1) (hb : d157946 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156458, d157946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156458, d157946, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d156463 q = 1) (hb : d157955 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156463, d157955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30667 q ha hb
    | true =>
      simp only [d156463, d157955, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156464 q = 1) (hb : d157956 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156464, d157956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156464, d157956, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156465 q = 1) (hb : d157957 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156465, d157957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156465, d157957, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156466 q = 1) (hb : d157958 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156466, d157958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156466, d157958, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156467 q = 1) (hb : d157959 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156467, d157959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156467, d157959, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156468 q = 1) (hb : d157960 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156468, d157960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156468, d157960, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  exact h9 p ha hb
theorem andIntro30669 (p : Pattern) (ha : d156456 p = 1) (hb : d157965 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156438 q = 1) (hb : d157939 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156438, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30664 q ha hb
    | true =>
      simp only [d156438, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156439 q = 1) (hb : d157940 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156439, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156439, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156453 q = 1) (hb : d157962 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156453, d157962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156453, d157962, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156454 q = 1) (hb : d157963 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156454, d157963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156454, d157963, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156455 q = 1) (hb : d157964 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156455, d157964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156455, d157964, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156456 q = 1) (hb : d157965 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156456, d157965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156456, d157965, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30670 (p : Pattern) (ha : d156475 p = 1) (hb : d157971 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156470 q = 1) (hb : d157966 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156470, d157966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30669 q ha hb
    | true =>
      simp only [d156470, d157966, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156471 q = 1) (hb : d157967 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156471, d157967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156471, d157967, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156472 q = 1) (hb : d157968 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156472, d157968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156472, d157968, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156473 q = 1) (hb : d157969 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156473, d157969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156473, d157969, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156474 q = 1) (hb : d157970 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156474, d157970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156474, d157970, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156475 q = 1) (hb : d157971 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156475, d157971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156475, d157971, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30671 (p : Pattern) (ha : d156481 p = 1) (hb : d157977 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156257 q = 1) (hb : d157764 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156257, d157764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156257, d157764, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30629 q ha hb
  have h2 (q : Pattern) (ha : d156258 q = 1) (hb : d157765 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156258, d157765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156258, d157765, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156267 q = 1) (hb : d157774 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156267, d157774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30629 q ha hb
    | true =>
      simp only [d156267, d157774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30632 q ha hb
  have h4 (q : Pattern) (ha : d156268 q = 1) (hb : d157775 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156268, d157775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156268, d157775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156269 q = 1) (hb : d157776 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156269, d157776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156269, d157776, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156347 q = 1) (hb : d157853 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156347, d157853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30643 q ha hb
    | true =>
      simp only [d156347, d157853, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30651 q ha hb
  have h7 (q : Pattern) (ha : d156365 q = 1) (hb : d157871 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156365, d157871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30652 q ha hb
    | true =>
      simp only [d156365, d157871, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30653 q ha hb
  have h8 (q : Pattern) (ha : d156366 q = 1) (hb : d157872 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156366, d157872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156366, d157872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156367 q = 1) (hb : d157873 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156367, d157873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156367, d157873, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h10 (q : Pattern) (ha : d156368 q = 1) (hb : d157874 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156368, d157874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156368, d157874, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156372 q = 1) (hb : d157878 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156372, d157878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156372, d157878, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30654 q ha hb
  have h12 (q : Pattern) (ha : d156374 q = 1) (hb : d157880 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156374, d157880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156374, d157880, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30655 q ha hb
  have h13 (q : Pattern) (ha : d156375 q = 1) (hb : d157881 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156375, d157881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d156375, d157881, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156376 q = 1) (hb : d157882 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156376, d157882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156376, d157882, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h15 (q : Pattern) (ha : d156377 q = 1) (hb : d157883 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156377, d157883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d156377, d157883, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h16 (q : Pattern) (ha : d156378 q = 1) (hb : d157884 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156378, d157884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156378, d157884, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156469 q = 1) (hb : d157961 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156469, d157961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156469, d157961, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30668 q ha hb
  have h18 (q : Pattern) (ha : d156476 q = 1) (hb : d157972 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156476, d157972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156476, d157972, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30670 q ha hb
  have h19 (q : Pattern) (ha : d156477 q = 1) (hb : d157973 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156477, d157973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d156477, d157973, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  have h20 (q : Pattern) (ha : d156478 q = 1) (hb : d157974 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156478, d157974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h19 q ha hb
    | true =>
      simp only [d156478, d157974, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h21 (q : Pattern) (ha : d156479 q = 1) (hb : d157975 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156479, d157975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h20 q ha hb
    | true =>
      simp only [d156479, d157975, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h22 (q : Pattern) (ha : d156480 q = 1) (hb : d157976 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156480, d157976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h21 q ha hb
    | true =>
      simp only [d156480, d157976, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h23 (q : Pattern) (ha : d156481 q = 1) (hb : d157977 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d156481, d157977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d156481, d157977, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h22 q ha hb
  exact h23 p ha hb
theorem andIntro30672 (p : Pattern) (ha : d156487 p = 1) (hb : d157983 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156482 q = 1) (hb : d157978 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d156482, d157978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156482, d157978, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30671 q ha hb
  have h2 (q : Pattern) (ha : d156483 q = 1) (hb : d157979 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d156483, d157979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156483, d157979, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156484 q = 1) (hb : d157980 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d156484, d157980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156484, d157980, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156485 q = 1) (hb : d157981 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d156485, d157981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156485, d157981, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156486 q = 1) (hb : d157982 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d156486, d157982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156486, d157982, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156487 q = 1) (hb : d157983 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d156487, d157983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156487, d157983, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30673 (p : Pattern) (ha : d156493 p = 1) (hb : d157989 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d155304 q = 1) (hb : d156872 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d155304, d156872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30424 q ha hb
    | true =>
      simp only [d155304, d156872, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30450 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155525 q = 1) (hb : d157110 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d155525, d157110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155525, d157110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30496 q ha hb
  have h3 (q : Pattern) (ha : d155526 q = 1) (hb : d157111 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d155526, d157111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d155526, d157111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155851 q = 1) (hb : d157385 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d155851, d157385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155851, d157385, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30556 q ha hb
  have h5 (q : Pattern) (ha : d155852 q = 1) (hb : d157386 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d155852, d157386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155852, d157386, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155853 q = 1) (hb : d157387 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d155853, d157387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155853, d157387, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156188 q = 1) (hb : d157702 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d156188, d157702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156188, d157702, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30616 q ha hb
  have h8 (q : Pattern) (ha : d156189 q = 1) (hb : d157703 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d156189, d157703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156189, d157703, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156190 q = 1) (hb : d157704 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d156190, d157704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156190, d157704, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156191 q = 1) (hb : d157705 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d156191, d157705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156191, d157705, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d156488 q = 1) (hb : d157984 q = 1) : d0 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d156488, d157984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156488, d157984, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30672 q ha hb
  have h12 (q : Pattern) (ha : d156489 q = 1) (hb : d157985 q = 1) : d0 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d156489, d157985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156489, d157985, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156490 q = 1) (hb : d157986 q = 1) : d0 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d156490, d157986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156490, d157986, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d156491 q = 1) (hb : d157987 q = 1) : d0 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d156491, d157987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156491, d157987, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d156492 q = 1) (hb : d157988 q = 1) : d0 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d156492, d157988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156492, d157988, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d156493 q = 1) (hb : d157989 q = 1) : d0 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d156493, d157989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156493, d157989, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
  exact h16 p ha hb
theorem andIntro30674 (p : Pattern) (ha : d156499 p = 1) (hb : d157995 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156494 q = 1) (hb : d157990 q = 1) : d0 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d156494, d157990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30673 q ha hb
    | true =>
      simp only [d156494, d157990, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156495 q = 1) (hb : d157991 q = 1) : d0 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d156495, d157991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156495, d157991, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156496 q = 1) (hb : d157992 q = 1) : d0 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d156496, d157992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156496, d157992, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156497 q = 1) (hb : d157993 q = 1) : d0 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d156497, d157993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156497, d157993, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156498 q = 1) (hb : d157994 q = 1) : d0 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d156498, d157994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156498, d157994, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156499 q = 1) (hb : d157995 q = 1) : d0 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d156499, d157995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156499, d157995, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30675 (p : Pattern) (ha : d156505 p = 1) (hb : d158001 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156500 q = 1) (hb : d157996 q = 1) : d0 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d156500, d157996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30674 q ha hb
    | true =>
      simp only [d156500, d157996, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156501 q = 1) (hb : d157997 q = 1) : d0 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d156501, d157997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156501, d157997, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156502 q = 1) (hb : d157998 q = 1) : d0 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d156502, d157998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156502, d157998, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156503 q = 1) (hb : d157999 q = 1) : d0 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d156503, d157999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156503, d157999, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156504 q = 1) (hb : d158000 q = 1) : d0 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d156504, d158000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156504, d158000, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156505 q = 1) (hb : d158001 q = 1) : d0 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d156505, d158001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156505, d158001, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30676 (p : Pattern) (ha : d156511 p = 1) (hb : d158007 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156506 q = 1) (hb : d158002 q = 1) : d0 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d156506, d158002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30675 q ha hb
    | true =>
      simp only [d156506, d158002, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156507 q = 1) (hb : d158003 q = 1) : d0 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d156507, d158003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156507, d158003, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156508 q = 1) (hb : d158004 q = 1) : d0 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d156508, d158004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156508, d158004, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156509 q = 1) (hb : d158005 q = 1) : d0 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d156509, d158005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156509, d158005, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156510 q = 1) (hb : d158006 q = 1) : d0 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d156510, d158006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156510, d158006, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156511 q = 1) (hb : d158007 q = 1) : d0 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d156511, d158007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156511, d158007, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30677 (p : Pattern) (ha : d156517 p = 1) (hb : d158013 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156512 q = 1) (hb : d158008 q = 1) : d0 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d156512, d158008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30676 q ha hb
    | true =>
      simp only [d156512, d158008, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156513 q = 1) (hb : d158009 q = 1) : d0 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d156513, d158009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156513, d158009, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156514 q = 1) (hb : d158010 q = 1) : d0 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d156514, d158010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156514, d158010, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156515 q = 1) (hb : d158011 q = 1) : d0 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d156515, d158011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156515, d158011, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156516 q = 1) (hb : d158012 q = 1) : d0 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d156516, d158012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156516, d158012, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156517 q = 1) (hb : d158013 q = 1) : d0 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d156517, d158013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156517, d158013, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30678 (p : Pattern) (ha : d156523 p = 1) (hb : d158019 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156518 q = 1) (hb : d158014 q = 1) : d0 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d156518, d158014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30677 q ha hb
    | true =>
      simp only [d156518, d158014, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156519 q = 1) (hb : d158015 q = 1) : d0 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d156519, d158015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156519, d158015, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156520 q = 1) (hb : d158016 q = 1) : d0 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d156520, d158016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156520, d158016, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156521 q = 1) (hb : d158017 q = 1) : d0 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d156521, d158017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156521, d158017, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156522 q = 1) (hb : d158018 q = 1) : d0 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d156522, d158018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156522, d158018, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156523 q = 1) (hb : d158019 q = 1) : d0 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d156523, d158019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156523, d158019, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30679 (p : Pattern) (ha : d156529 p = 1) (hb : d158025 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156524 q = 1) (hb : d158020 q = 1) : d0 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d156524, d158020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30678 q ha hb
    | true =>
      simp only [d156524, d158020, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156525 q = 1) (hb : d158021 q = 1) : d0 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d156525, d158021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156525, d158021, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156526 q = 1) (hb : d158022 q = 1) : d0 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d156526, d158022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156526, d158022, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156527 q = 1) (hb : d158023 q = 1) : d0 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d156527, d158023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156527, d158023, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156528 q = 1) (hb : d158024 q = 1) : d0 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d156528, d158024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156528, d158024, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156529 q = 1) (hb : d158025 q = 1) : d0 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d156529, d158025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156529, d158025, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30680 (p : Pattern) (ha : d156535 p = 1) (hb : d158031 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156530 q = 1) (hb : d158026 q = 1) : d0 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d156530, d158026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30679 q ha hb
    | true =>
      simp only [d156530, d158026, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156531 q = 1) (hb : d158027 q = 1) : d0 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d156531, d158027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156531, d158027, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d156532 q = 1) (hb : d158028 q = 1) : d0 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d156532, d158028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156532, d158028, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156533 q = 1) (hb : d158029 q = 1) : d0 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d156533, d158029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156533, d158029, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d156534 q = 1) (hb : d158030 q = 1) : d0 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d156534, d158030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156534, d158030, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h6 (q : Pattern) (ha : d156535 q = 1) (hb : d158031 q = 1) : d0 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d156535, d158031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156535, d158031, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h6 p ha hb
theorem andIntro30681 (p : Pattern) (ha : d53647 p = 1) (hb : d152855 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d112 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30061 q ha hb
    | true =>
      simp only [d112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30062 q ha hb
  have h2 (q : Pattern) (ha : d113 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d53637 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d53637, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d53638 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53638, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d407 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d407, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30081 q ha hb
  have h6 (q : Pattern) (ha : d53639 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d53639, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d53640 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d53640, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d53641 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d53641, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d53642 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d53642, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d463 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d463, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30082 q ha hb
  have h11 (q : Pattern) (ha : d53643 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d53643, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d53644 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d53644, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d53645 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d53645, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d53646 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d53646, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d53647 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
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
theorem andIntro30682 (p : Pattern) (ha : d150329 p = 1) (hb : d152855 p = 1) : d156818 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12241 q = 1) (hb : d152855 q = 1) : d156562 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12241, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30073 q ha hb
    | true =>
      simp only [d12241, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30053 q ha hb
  have h2 (q : Pattern) (ha : d12292 q = 1) (hb : d152855 q = 1) : d156620 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12292, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12292, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12293 q = 1) (hb : d152855 q = 1) : d156621 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12293, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12293, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12294 q = 1) (hb : d152855 q = 1) : d156622 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12294, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12294, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12295 q = 1) (hb : d152855 q = 1) : d156623 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12295, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12295, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150329 q = 1) (hb : d152855 q = 1) : d156818 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150329, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150329, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30683 (p : Pattern) (ha : d150339 p = 1) (hb : d152855 p = 1) : d156859 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12268 q = 1) (hb : d152855 q = 1) : d156596 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12268, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30078 q ha hb
    | true =>
      simp only [d12268, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30058 q ha hb
  have h2 (q : Pattern) (ha : d150335 q = 1) (hb : d152855 q = 1) : d156855 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150335, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150335, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150336 q = 1) (hb : d152855 q = 1) : d156856 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150336, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150336, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150337 q = 1) (hb : d152855 q = 1) : d156857 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150337, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150337, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150338 q = 1) (hb : d152855 q = 1) : d156858 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150338, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150338, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150339 q = 1) (hb : d152855 q = 1) : d156859 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150339, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150339, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30684 (p : Pattern) (ha : d150345 p = 1) (hb : d152855 p = 1) : d158042 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12297 q = 1) (hb : d152855 q = 1) : d156625 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12297, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30083 q ha hb
    | true =>
      simp only [d12297, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30084 q ha hb
  have h2 (q : Pattern) (ha : d12298 q = 1) (hb : d152855 q = 1) : d156626 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12298, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12298, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150327 q = 1) (hb : d152855 q = 1) : d158032 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150327, d158032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150327, d158032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150328 q = 1) (hb : d152855 q = 1) : d158033 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150328, d158033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150328, d158033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150330 q = 1) (hb : d152855 q = 1) : d156819 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150330, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150330, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30682 q ha hb
  have h6 (q : Pattern) (ha : d150331 q = 1) (hb : d152855 q = 1) : d158034 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150331, d158034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150331, d158034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150332 q = 1) (hb : d152855 q = 1) : d158035 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150332, d158035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150332, d158035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150333 q = 1) (hb : d152855 q = 1) : d158036 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150333, d158036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150333, d158036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150334 q = 1) (hb : d152855 q = 1) : d158037 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150334, d158037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150334, d158037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150340 q = 1) (hb : d152855 q = 1) : d156860 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150340, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150340, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30683 q ha hb
  have h11 (q : Pattern) (ha : d150341 q = 1) (hb : d152855 q = 1) : d158038 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150341, d158038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150341, d158038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150342 q = 1) (hb : d152855 q = 1) : d158039 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150342, d158039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150342, d158039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150343 q = 1) (hb : d152855 q = 1) : d158040 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150343, d158040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150343, d158040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150344 q = 1) (hb : d152855 q = 1) : d158041 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150344, d158041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150344, d158041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150345 q = 1) (hb : d152855 q = 1) : d158042 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150345, d158042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150345, d158042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30685 (p : Pattern) (ha : d150351 p = 1) (hb : d152855 p = 1) : d158048 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d53648 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53648, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30681 q ha hb
  have h2 (q : Pattern) (ha : d53649 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53649, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d53650 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53650, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d53651 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53651, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d53652 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d53652, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150346 q = 1) (hb : d152855 q = 1) : d158043 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150346, d158043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150346, d158043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30684 q ha hb
  have h7 (q : Pattern) (ha : d150347 q = 1) (hb : d152855 q = 1) : d158044 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150347, d158044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150347, d158044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d150348 q = 1) (hb : d152855 q = 1) : d158045 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150348, d158045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150348, d158045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150349 q = 1) (hb : d152855 q = 1) : d158046 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150349, d158046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150349, d158046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150350 q = 1) (hb : d152855 q = 1) : d158047 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150350, d158047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150350, d158047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150351 q = 1) (hb : d152855 q = 1) : d158048 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150351, d158048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150351, d158048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  exact h11 p ha hb
theorem andIntro30686 (p : Pattern) (ha : d150354 p = 1) (hb : d152855 p = 1) : d158051 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12463 q = 1) (hb : d152855 q = 1) : d156675 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12463, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30112 q ha hb
    | true =>
      simp only [d12463, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30113 q ha hb
  have h2 (q : Pattern) (ha : d12464 q = 1) (hb : d152855 q = 1) : d156738 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12464, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12464, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12465 q = 1) (hb : d152855 q = 1) : d156739 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12465, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12465, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12466 q = 1) (hb : d152855 q = 1) : d156740 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12466, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12466, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12467 q = 1) (hb : d152855 q = 1) : d156741 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12467, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12467, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150354 q = 1) (hb : d152855 q = 1) : d158051 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150354, d158051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150354, d158051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30687 (p : Pattern) (ha : d150365 p = 1) (hb : d152855 p = 1) : d158061 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150360 q = 1) (hb : d152855 q = 1) : d156713 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150360, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30146 q ha hb
    | true =>
      simp only [d150360, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30119 q ha hb
  have h2 (q : Pattern) (ha : d150361 q = 1) (hb : d152855 q = 1) : d158057 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150361, d158057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150361, d158057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150362 q = 1) (hb : d152855 q = 1) : d158058 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150362, d158058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150362, d158058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150363 q = 1) (hb : d152855 q = 1) : d158059 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150363, d158059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150363, d158059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150364 q = 1) (hb : d152855 q = 1) : d158060 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150364, d158060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150364, d158060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150365 q = 1) (hb : d152855 q = 1) : d158061 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150365, d158061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150365, d158061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30688 (p : Pattern) (ha : d150371 p = 1) (hb : d152855 p = 1) : d158067 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12469 q = 1) (hb : d152855 q = 1) : d156743 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12469, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30111 q ha hb
    | true =>
      simp only [d12469, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30114 q ha hb
  have h2 (q : Pattern) (ha : d12470 q = 1) (hb : d152855 q = 1) : d156744 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12470, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12470, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150352 q = 1) (hb : d152855 q = 1) : d158049 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150352, d158049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150352, d158049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150353 q = 1) (hb : d152855 q = 1) : d158050 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150353, d158050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150353, d158050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150355 q = 1) (hb : d152855 q = 1) : d158052 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150355, d158052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150355, d158052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30686 q ha hb
  have h6 (q : Pattern) (ha : d150356 q = 1) (hb : d152855 q = 1) : d158053 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150356, d158053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150356, d158053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150357 q = 1) (hb : d152855 q = 1) : d158054 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150357, d158054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150357, d158054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150358 q = 1) (hb : d152855 q = 1) : d158055 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150358, d158055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150358, d158055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150359 q = 1) (hb : d152855 q = 1) : d158056 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150359, d158056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150359, d158056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150366 q = 1) (hb : d152855 q = 1) : d158062 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150366, d158062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150366, d158062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30687 q ha hb
  have h11 (q : Pattern) (ha : d150367 q = 1) (hb : d152855 q = 1) : d158063 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150367, d158063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150367, d158063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150368 q = 1) (hb : d152855 q = 1) : d158064 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150368, d158064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150368, d158064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150369 q = 1) (hb : d152855 q = 1) : d158065 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150369, d158065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150369, d158065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150370 q = 1) (hb : d152855 q = 1) : d158066 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150370, d158066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150370, d158066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150371 q = 1) (hb : d152855 q = 1) : d158067 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150371, d158067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150371, d158067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30689 (p : Pattern) (ha : d150377 p = 1) (hb : d152855 p = 1) : d158073 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150372 q = 1) (hb : d152855 q = 1) : d158068 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150372, d158068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150372, d158068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30688 q ha hb
  have h2 (q : Pattern) (ha : d150373 q = 1) (hb : d152855 q = 1) : d158069 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150373, d158069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150373, d158069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150374 q = 1) (hb : d152855 q = 1) : d158070 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150374, d158070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150374, d158070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150375 q = 1) (hb : d152855 q = 1) : d158071 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150375, d158071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150375, d158071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150376 q = 1) (hb : d152855 q = 1) : d158072 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150376, d158072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150376, d158072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150377 q = 1) (hb : d152855 q = 1) : d158073 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150377, d158073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150377, d158073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30690 (p : Pattern) (ha : d150381 p = 1) (hb : d152855 p = 1) : d158077 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12718 q = 1) (hb : d152855 q = 1) : d156909 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12718, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30159 q ha hb
    | true =>
      simp only [d12718, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30160 q ha hb
  have h2 (q : Pattern) (ha : d12719 q = 1) (hb : d152855 q = 1) : d156910 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12719, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12719, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12720 q = 1) (hb : d152855 q = 1) : d156911 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12720, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12720, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12721 q = 1) (hb : d152855 q = 1) : d156912 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12721, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12721, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12722 q = 1) (hb : d152855 q = 1) : d156913 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12722, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12722, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150381 q = 1) (hb : d152855 q = 1) : d158077 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150381, d158077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150381, d158077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30691 (p : Pattern) (ha : d150392 p = 1) (hb : d152855 p = 1) : d158088 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150387 q = 1) (hb : d152855 q = 1) : d158083 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150387, d158083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30195 q ha hb
    | true =>
      simp only [d150387, d158083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30168 q ha hb
  have h2 (q : Pattern) (ha : d150388 q = 1) (hb : d152855 q = 1) : d158084 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150388, d158084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150388, d158084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150389 q = 1) (hb : d152855 q = 1) : d158085 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150389, d158085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150389, d158085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150390 q = 1) (hb : d152855 q = 1) : d158086 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150390, d158086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150390, d158086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150391 q = 1) (hb : d152855 q = 1) : d158087 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150391, d158087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150391, d158087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150392 q = 1) (hb : d152855 q = 1) : d158088 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150392, d158088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150392, d158088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30692 (p : Pattern) (ha : d150398 p = 1) (hb : d152855 p = 1) : d158094 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12724 q = 1) (hb : d152855 q = 1) : d156915 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12724, d156915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30158 q ha hb
    | true =>
      simp only [d12724, d156915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30161 q ha hb
  have h2 (q : Pattern) (ha : d12725 q = 1) (hb : d152855 q = 1) : d156916 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12725, d156916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12725, d156916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150379 q = 1) (hb : d152855 q = 1) : d158075 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150379, d158075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150379, d158075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150380 q = 1) (hb : d152855 q = 1) : d158076 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150380, d158076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150380, d158076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150382 q = 1) (hb : d152855 q = 1) : d158078 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150382, d158078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150382, d158078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30690 q ha hb
  have h6 (q : Pattern) (ha : d150383 q = 1) (hb : d152855 q = 1) : d158079 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150383, d158079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150383, d158079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150384 q = 1) (hb : d152855 q = 1) : d158080 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150384, d158080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150384, d158080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150385 q = 1) (hb : d152855 q = 1) : d158081 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150385, d158081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150385, d158081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150386 q = 1) (hb : d152855 q = 1) : d158082 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150386, d158082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150386, d158082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150393 q = 1) (hb : d152855 q = 1) : d158089 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150393, d158089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150393, d158089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30691 q ha hb
  have h11 (q : Pattern) (ha : d150394 q = 1) (hb : d152855 q = 1) : d158090 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150394, d158090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150394, d158090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150395 q = 1) (hb : d152855 q = 1) : d158091 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150395, d158091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150395, d158091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150396 q = 1) (hb : d152855 q = 1) : d158092 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150396, d158092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150396, d158092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150397 q = 1) (hb : d152855 q = 1) : d158093 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150397, d158093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150397, d158093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150398 q = 1) (hb : d152855 q = 1) : d158094 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150398, d158094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150398, d158094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30693 (p : Pattern) (ha : d150404 p = 1) (hb : d152855 p = 1) : d158100 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150399 q = 1) (hb : d152855 q = 1) : d158095 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150399, d158095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150399, d158095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30692 q ha hb
  have h2 (q : Pattern) (ha : d150400 q = 1) (hb : d152855 q = 1) : d158096 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150400, d158096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150400, d158096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150401 q = 1) (hb : d152855 q = 1) : d158097 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150401, d158097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150401, d158097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150402 q = 1) (hb : d152855 q = 1) : d158098 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150402, d158098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150402, d158098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150403 q = 1) (hb : d152855 q = 1) : d158099 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150403, d158099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150403, d158099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150404 q = 1) (hb : d152855 q = 1) : d158100 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150404, d158100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150404, d158100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30694 (p : Pattern) (ha : d150409 p = 1) (hb : d152855 p = 1) : d158105 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12992 q = 1) (hb : d152855 q = 1) : d157167 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d12992, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30213 q ha hb
    | true =>
      simp only [d12992, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30214 q ha hb
  have h2 (q : Pattern) (ha : d12993 q = 1) (hb : d152855 q = 1) : d157168 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d12993, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12993, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d12994 q = 1) (hb : d152855 q = 1) : d157169 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d12994, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d12994, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d12995 q = 1) (hb : d152855 q = 1) : d157170 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d12995, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12995, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d12996 q = 1) (hb : d152855 q = 1) : d157171 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d12996, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d12996, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150409 q = 1) (hb : d152855 q = 1) : d158105 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150409, d158105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150409, d158105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30695 (p : Pattern) (ha : d150418 p = 1) (hb : d152855 p = 1) : d157349 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13244 q = 1) (hb : d152855 q = 1) : d157336 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13244, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30256 q ha hb
    | true =>
      simp only [d13244, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13245 q = 1) (hb : d152855 q = 1) : d157337 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13245, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13245, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13197 q = 1) (hb : d152855 q = 1) : d157344 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13197, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30223 q ha hb
    | true =>
      simp only [d13197, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13198 q = 1) (hb : d152855 q = 1) : d157345 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13198, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13198, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150415 q = 1) (hb : d152855 q = 1) : d157346 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150415, d157346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150415, d157346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150416 q = 1) (hb : d152855 q = 1) : d157347 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150416, d157347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150416, d157347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150417 q = 1) (hb : d152855 q = 1) : d157348 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150417, d157348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150417, d157348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150418 q = 1) (hb : d152855 q = 1) : d157349 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150418, d157349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150418, d157349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30696 (p : Pattern) (ha : d150424 p = 1) (hb : d152855 p = 1) : d158116 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150419 q = 1) (hb : d152855 q = 1) : d158111 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150419, d158111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30695 q ha hb
    | true =>
      simp only [d150419, d158111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30224 q ha hb
  have h2 (q : Pattern) (ha : d150420 q = 1) (hb : d152855 q = 1) : d158112 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150420, d158112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150420, d158112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150421 q = 1) (hb : d152855 q = 1) : d158113 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150421, d158113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150421, d158113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150422 q = 1) (hb : d152855 q = 1) : d158114 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150422, d158114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150422, d158114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150423 q = 1) (hb : d152855 q = 1) : d158115 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150423, d158115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150423, d158115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150424 q = 1) (hb : d152855 q = 1) : d158116 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150424, d158116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150424, d158116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30697 (p : Pattern) (ha : d150430 p = 1) (hb : d152855 p = 1) : d158122 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d12998 q = 1) (hb : d152855 q = 1) : d157173 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d12998, d157173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30212 q ha hb
    | true =>
      simp only [d12998, d157173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30215 q ha hb
  have h2 (q : Pattern) (ha : d12999 q = 1) (hb : d152855 q = 1) : d157174 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d12999, d157174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d12999, d157174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150407 q = 1) (hb : d152855 q = 1) : d158103 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150407, d158103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150407, d158103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150408 q = 1) (hb : d152855 q = 1) : d158104 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150408, d158104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150408, d158104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150410 q = 1) (hb : d152855 q = 1) : d158106 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150410, d158106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150410, d158106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30694 q ha hb
  have h6 (q : Pattern) (ha : d150411 q = 1) (hb : d152855 q = 1) : d158107 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150411, d158107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150411, d158107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150412 q = 1) (hb : d152855 q = 1) : d158108 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150412, d158108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150412, d158108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150413 q = 1) (hb : d152855 q = 1) : d158109 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150413, d158109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150413, d158109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150414 q = 1) (hb : d152855 q = 1) : d158110 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150414, d158110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150414, d158110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150425 q = 1) (hb : d152855 q = 1) : d158117 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150425, d158117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150425, d158117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30696 q ha hb
  have h11 (q : Pattern) (ha : d150426 q = 1) (hb : d152855 q = 1) : d158118 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150426, d158118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150426, d158118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150427 q = 1) (hb : d152855 q = 1) : d158119 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150427, d158119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150427, d158119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150428 q = 1) (hb : d152855 q = 1) : d158120 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150428, d158120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150428, d158120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150429 q = 1) (hb : d152855 q = 1) : d158121 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150429, d158121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150429, d158121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150430 q = 1) (hb : d152855 q = 1) : d158122 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150430, d158122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150430, d158122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30698 (p : Pattern) (ha : d150436 p = 1) (hb : d152855 p = 1) : d158128 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150431 q = 1) (hb : d152855 q = 1) : d158123 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150431, d158123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150431, d158123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30697 q ha hb
  have h2 (q : Pattern) (ha : d150432 q = 1) (hb : d152855 q = 1) : d158124 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150432, d158124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150432, d158124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150433 q = 1) (hb : d152855 q = 1) : d158125 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150433, d158125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150433, d158125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150434 q = 1) (hb : d152855 q = 1) : d158126 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150434, d158126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150434, d158126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150435 q = 1) (hb : d152855 q = 1) : d158127 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150435, d158127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150435, d158127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150436 q = 1) (hb : d152855 q = 1) : d158128 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150436, d158128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150436, d158128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30699 (p : Pattern) (ha : d150442 p = 1) (hb : d152855 p = 1) : d158134 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13318 q = 1) (hb : d152855 q = 1) : d157455 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13318, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30274 q ha hb
    | true =>
      simp only [d13318, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30275 q ha hb
  have h2 (q : Pattern) (ha : d13319 q = 1) (hb : d152855 q = 1) : d157456 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13319, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13319, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13320 q = 1) (hb : d152855 q = 1) : d157457 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13320, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13320, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13321 q = 1) (hb : d152855 q = 1) : d157458 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13321, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13321, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13322 q = 1) (hb : d152855 q = 1) : d157459 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13322, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13322, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150442 q = 1) (hb : d152855 q = 1) : d158134 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150442, d158134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150442, d158134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30700 (p : Pattern) (ha : d150451 p = 1) (hb : d152855 p = 1) : d158143 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13570 q = 1) (hb : d152855 q = 1) : d157667 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13570, d157667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30317 q ha hb
    | true =>
      simp only [d13570, d157667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13571 q = 1) (hb : d152855 q = 1) : d157668 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13571, d157668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13571, d157668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13523 q = 1) (hb : d152855 q = 1) : d157657 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13523, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30284 q ha hb
    | true =>
      simp only [d13523, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13524 q = 1) (hb : d152855 q = 1) : d157658 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13524, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13524, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150448 q = 1) (hb : d152855 q = 1) : d158140 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150448, d158140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150448, d158140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150449 q = 1) (hb : d152855 q = 1) : d158141 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150449, d158141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150449, d158141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150450 q = 1) (hb : d152855 q = 1) : d158142 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150450, d158142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150450, d158142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150451 q = 1) (hb : d152855 q = 1) : d158143 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150451, d158143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150451, d158143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30701 (p : Pattern) (ha : d150457 p = 1) (hb : d152855 p = 1) : d158149 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150452 q = 1) (hb : d152855 q = 1) : d158144 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150452, d158144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30700 q ha hb
    | true =>
      simp only [d150452, d158144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30285 q ha hb
  have h2 (q : Pattern) (ha : d150453 q = 1) (hb : d152855 q = 1) : d158145 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150453, d158145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150453, d158145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150454 q = 1) (hb : d152855 q = 1) : d158146 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150454, d158146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150454, d158146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150455 q = 1) (hb : d152855 q = 1) : d158147 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150455, d158147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150455, d158147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150456 q = 1) (hb : d152855 q = 1) : d158148 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150456, d158148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150456, d158148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150457 q = 1) (hb : d152855 q = 1) : d158149 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150457, d158149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150457, d158149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30702 (p : Pattern) (ha : d150463 p = 1) (hb : d152855 p = 1) : d158155 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13324 q = 1) (hb : d152855 q = 1) : d157461 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13324, d157461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30273 q ha hb
    | true =>
      simp only [d13324, d157461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30276 q ha hb
  have h2 (q : Pattern) (ha : d13325 q = 1) (hb : d152855 q = 1) : d157462 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13325, d157462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13325, d157462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150440 q = 1) (hb : d152855 q = 1) : d158132 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150440, d158132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150440, d158132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150441 q = 1) (hb : d152855 q = 1) : d158133 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150441, d158133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150441, d158133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150443 q = 1) (hb : d152855 q = 1) : d158135 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150443, d158135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150443, d158135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30699 q ha hb
  have h6 (q : Pattern) (ha : d150444 q = 1) (hb : d152855 q = 1) : d158136 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150444, d158136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150444, d158136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150445 q = 1) (hb : d152855 q = 1) : d158137 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150445, d158137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150445, d158137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150446 q = 1) (hb : d152855 q = 1) : d158138 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150446, d158138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150446, d158138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150447 q = 1) (hb : d152855 q = 1) : d158139 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150447, d158139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150447, d158139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150458 q = 1) (hb : d152855 q = 1) : d158150 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150458, d158150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150458, d158150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30701 q ha hb
  have h11 (q : Pattern) (ha : d150459 q = 1) (hb : d152855 q = 1) : d158151 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150459, d158151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150459, d158151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150460 q = 1) (hb : d152855 q = 1) : d158152 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150460, d158152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150460, d158152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150461 q = 1) (hb : d152855 q = 1) : d158153 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150461, d158153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150461, d158153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150462 q = 1) (hb : d152855 q = 1) : d158154 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150462, d158154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150462, d158154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150463 q = 1) (hb : d152855 q = 1) : d158155 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150463, d158155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150463, d158155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30703 (p : Pattern) (ha : d150469 p = 1) (hb : d152855 p = 1) : d158161 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150464 q = 1) (hb : d152855 q = 1) : d158156 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150464, d158156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150464, d158156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30702 q ha hb
  have h2 (q : Pattern) (ha : d150465 q = 1) (hb : d152855 q = 1) : d158157 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150465, d158157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150465, d158157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150466 q = 1) (hb : d152855 q = 1) : d158158 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150466, d158158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150466, d158158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150467 q = 1) (hb : d152855 q = 1) : d158159 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150467, d158159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150467, d158159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150468 q = 1) (hb : d152855 q = 1) : d158160 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150468, d158160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150468, d158160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150469 q = 1) (hb : d152855 q = 1) : d158161 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150469, d158161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150469, d158161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30704 (p : Pattern) (ha : d150476 p = 1) (hb : d152855 p = 1) : d158168 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13645 q = 1) (hb : d152855 q = 1) : d157768 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d13645, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30335 q ha hb
    | true =>
      simp only [d13645, d157768, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30336 q ha hb
  have h2 (q : Pattern) (ha : d13646 q = 1) (hb : d152855 q = 1) : d157769 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d13646, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13646, d157769, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13647 q = 1) (hb : d152855 q = 1) : d157770 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d13647, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d13647, d157770, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13648 q = 1) (hb : d152855 q = 1) : d157771 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d13648, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13648, d157771, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d13649 q = 1) (hb : d152855 q = 1) : d157772 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d13649, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13649, d157772, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150476 q = 1) (hb : d152855 q = 1) : d158168 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150476, d158168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150476, d158168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30705 (p : Pattern) (ha : d150485 p = 1) (hb : d152855 p = 1) : d158177 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13897 q = 1) (hb : d152855 q = 1) : d157949 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13897, d157949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30378 q ha hb
    | true =>
      simp only [d13897, d157949, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d13898 q = 1) (hb : d152855 q = 1) : d157950 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13898, d157950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13898, d157950, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d13850 q = 1) (hb : d152855 q = 1) : d157939 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d13850, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30345 q ha hb
    | true =>
      simp only [d13850, d157939, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d13851 q = 1) (hb : d152855 q = 1) : d157940 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d13851, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d13851, d157940, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150482 q = 1) (hb : d152855 q = 1) : d158174 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d150482, d158174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150482, d158174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150483 q = 1) (hb : d152855 q = 1) : d158175 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d150483, d158175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150483, d158175, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150484 q = 1) (hb : d152855 q = 1) : d158176 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d150484, d158176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150484, d158176, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150485 q = 1) (hb : d152855 q = 1) : d158177 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d150485, d158177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150485, d158177, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h8 p ha hb
theorem andIntro30706 (p : Pattern) (ha : d150491 p = 1) (hb : d152855 p = 1) : d158183 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150486 q = 1) (hb : d152855 q = 1) : d158178 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d150486, d158178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30705 q ha hb
    | true =>
      simp only [d150486, d158178, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30346 q ha hb
  have h2 (q : Pattern) (ha : d150487 q = 1) (hb : d152855 q = 1) : d158179 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d150487, d158179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150487, d158179, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150488 q = 1) (hb : d152855 q = 1) : d158180 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d150488, d158180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150488, d158180, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150489 q = 1) (hb : d152855 q = 1) : d158181 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d150489, d158181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150489, d158181, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150490 q = 1) (hb : d152855 q = 1) : d158182 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d150490, d158182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150490, d158182, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150491 q = 1) (hb : d152855 q = 1) : d158183 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d150491, d158183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150491, d158183, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30707 (p : Pattern) (ha : d150497 p = 1) (hb : d152855 p = 1) : d158189 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d13651 q = 1) (hb : d152855 q = 1) : d157774 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d13651, d157774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30334 q ha hb
    | true =>
      simp only [d13651, d157774, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30337 q ha hb
  have h2 (q : Pattern) (ha : d13652 q = 1) (hb : d152855 q = 1) : d157775 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d13652, d157775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d13652, d157775, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150474 q = 1) (hb : d152855 q = 1) : d158166 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150474, d158166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150474, d158166, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150475 q = 1) (hb : d152855 q = 1) : d158167 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150475, d158167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150475, d158167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150477 q = 1) (hb : d152855 q = 1) : d158169 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150477, d158169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150477, d158169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30704 q ha hb
  have h6 (q : Pattern) (ha : d150478 q = 1) (hb : d152855 q = 1) : d158170 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150478, d158170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150478, d158170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h7 (q : Pattern) (ha : d150479 q = 1) (hb : d152855 q = 1) : d158171 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150479, d158171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150479, d158171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h8 (q : Pattern) (ha : d150480 q = 1) (hb : d152855 q = 1) : d158172 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150480, d158172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d150480, d158172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h9 (q : Pattern) (ha : d150481 q = 1) (hb : d152855 q = 1) : d158173 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150481, d158173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150481, d158173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150492 q = 1) (hb : d152855 q = 1) : d158184 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d150492, d158184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150492, d158184, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30706 q ha hb
  have h11 (q : Pattern) (ha : d150493 q = 1) (hb : d152855 q = 1) : d158185 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d150493, d158185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150493, d158185, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h12 (q : Pattern) (ha : d150494 q = 1) (hb : d152855 q = 1) : d158186 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d150494, d158186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d150494, d158186, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h13 (q : Pattern) (ha : d150495 q = 1) (hb : d152855 q = 1) : d158187 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d150495, d158187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d150495, d158187, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h14 (q : Pattern) (ha : d150496 q = 1) (hb : d152855 q = 1) : d158188 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d150496, d158188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d150496, d158188, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h15 (q : Pattern) (ha : d150497 q = 1) (hb : d152855 q = 1) : d158189 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d150497, d158189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d150497, d158189, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  exact h15 p ha hb
theorem andIntro30708 (p : Pattern) (ha : d150503 p = 1) (hb : d152855 p = 1) : d158195 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150498 q = 1) (hb : d152855 q = 1) : d158190 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d150498, d158190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150498, d158190, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30707 q ha hb
  have h2 (q : Pattern) (ha : d150499 q = 1) (hb : d152855 q = 1) : d158191 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d150499, d158191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150499, d158191, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d150500 q = 1) (hb : d152855 q = 1) : d158192 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d150500, d158192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150500, d158192, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150501 q = 1) (hb : d152855 q = 1) : d158193 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d150501, d158193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150501, d158193, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d150502 q = 1) (hb : d152855 q = 1) : d158194 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d150502, d158194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150502, d158194, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150503 q = 1) (hb : d152855 q = 1) : d158195 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d150503, d158195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150503, d158195, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30709 (p : Pattern) (ha : d150509 p = 1) (hb : d152855 p = 1) : d158201 p = 1 := by
  have h0 (q : Pattern) (ha : d150378 q = 1) (hb : d152855 q = 1) : d158074 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150378, d158074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30685 q ha hb
    | true =>
      simp only [d150378, d158074, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30689 q ha hb
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d150405 q = 1) (hb : d152855 q = 1) : d158101 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150405, d158101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150405, d158101, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30693 q ha hb
  have h3 (q : Pattern) (ha : d150406 q = 1) (hb : d152855 q = 1) : d158102 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150406, d158102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
    | true =>
      simp only [d150406, d158102, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d150437 q = 1) (hb : d152855 q = 1) : d158129 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150437, d158129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150437, d158129, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30698 q ha hb
  have h5 (q : Pattern) (ha : d150438 q = 1) (hb : d152855 q = 1) : d158130 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150438, d158130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150438, d158130, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d150439 q = 1) (hb : d152855 q = 1) : d158131 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150439, d158131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150439, d158131, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d150470 q = 1) (hb : d152855 q = 1) : d158162 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150470, d158162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150470, d158162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30703 q ha hb
  have h8 (q : Pattern) (ha : d150471 q = 1) (hb : d152855 q = 1) : d158163 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150471, d158163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150471, d158163, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d150472 q = 1) (hb : d152855 q = 1) : d158164 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150472, d158164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150472, d158164, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d150473 q = 1) (hb : d152855 q = 1) : d158165 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150473, d158165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d150473, d158165, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  have h11 (q : Pattern) (ha : d150504 q = 1) (hb : d152855 q = 1) : d158196 q = 1 := by
    cases bit : q 10254 with
    | false =>
      simp only [d150504, d158196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150504, d158196, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30708 q ha hb
  have h12 (q : Pattern) (ha : d150505 q = 1) (hb : d152855 q = 1) : d158197 q = 1 := by
    cases bit : q 10253 with
    | false =>
      simp only [d150505, d158197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150505, d158197, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d150506 q = 1) (hb : d152855 q = 1) : d158198 q = 1 := by
    cases bit : q 10252 with
    | false =>
      simp only [d150506, d158198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150506, d158198, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d150507 q = 1) (hb : d152855 q = 1) : d158199 q = 1 := by
    cases bit : q 10251 with
    | false =>
      simp only [d150507, d158199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150507, d158199, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d150508 q = 1) (hb : d152855 q = 1) : d158200 q = 1 := by
    cases bit : q 10250 with
    | false =>
      simp only [d150508, d158200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d150508, d158200, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
  have h16 (q : Pattern) (ha : d150509 q = 1) (hb : d152855 q = 1) : d158201 q = 1 := by
    cases bit : q 260 with
    | false =>
      simp only [d150509, d158201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d150509, d158201, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  exact h16 p ha hb
theorem andIntro30710 (p : Pattern) (ha : d150515 p = 1) (hb : d152855 p = 1) : d158207 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150510 q = 1) (hb : d152855 q = 1) : d158202 q = 1 := by
    cases bit : q 259 with
    | false =>
      simp only [d150510, d158202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30709 q ha hb
    | true =>
      simp only [d150510, d158202, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150511 q = 1) (hb : d152855 q = 1) : d158203 q = 1 := by
    cases bit : q 258 with
    | false =>
      simp only [d150511, d158203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150511, d158203, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150512 q = 1) (hb : d152855 q = 1) : d158204 q = 1 := by
    cases bit : q 257 with
    | false =>
      simp only [d150512, d158204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150512, d158204, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150513 q = 1) (hb : d152855 q = 1) : d158205 q = 1 := by
    cases bit : q 256 with
    | false =>
      simp only [d150513, d158205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150513, d158205, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150514 q = 1) (hb : d152855 q = 1) : d158206 q = 1 := by
    cases bit : q 255 with
    | false =>
      simp only [d150514, d158206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150514, d158206, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150515 q = 1) (hb : d152855 q = 1) : d158207 q = 1 := by
    cases bit : q 254 with
    | false =>
      simp only [d150515, d158207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150515, d158207, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30711 (p : Pattern) (ha : d150521 p = 1) (hb : d152855 p = 1) : d158213 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150516 q = 1) (hb : d152855 q = 1) : d158208 q = 1 := by
    cases bit : q 253 with
    | false =>
      simp only [d150516, d158208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30710 q ha hb
    | true =>
      simp only [d150516, d158208, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150517 q = 1) (hb : d152855 q = 1) : d158209 q = 1 := by
    cases bit : q 252 with
    | false =>
      simp only [d150517, d158209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150517, d158209, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150518 q = 1) (hb : d152855 q = 1) : d158210 q = 1 := by
    cases bit : q 251 with
    | false =>
      simp only [d150518, d158210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150518, d158210, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150519 q = 1) (hb : d152855 q = 1) : d158211 q = 1 := by
    cases bit : q 250 with
    | false =>
      simp only [d150519, d158211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150519, d158211, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150520 q = 1) (hb : d152855 q = 1) : d158212 q = 1 := by
    cases bit : q 249 with
    | false =>
      simp only [d150520, d158212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150520, d158212, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150521 q = 1) (hb : d152855 q = 1) : d158213 q = 1 := by
    cases bit : q 245 with
    | false =>
      simp only [d150521, d158213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150521, d158213, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30712 (p : Pattern) (ha : d150527 p = 1) (hb : d152855 p = 1) : d158219 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150522 q = 1) (hb : d152855 q = 1) : d158214 q = 1 := by
    cases bit : q 200 with
    | false =>
      simp only [d150522, d158214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30711 q ha hb
    | true =>
      simp only [d150522, d158214, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150523 q = 1) (hb : d152855 q = 1) : d158215 q = 1 := by
    cases bit : q 199 with
    | false =>
      simp only [d150523, d158215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150523, d158215, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150524 q = 1) (hb : d152855 q = 1) : d158216 q = 1 := by
    cases bit : q 186 with
    | false =>
      simp only [d150524, d158216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150524, d158216, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150525 q = 1) (hb : d152855 q = 1) : d158217 q = 1 := by
    cases bit : q 185 with
    | false =>
      simp only [d150525, d158217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150525, d158217, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150526 q = 1) (hb : d152855 q = 1) : d158218 q = 1 := by
    cases bit : q 184 with
    | false =>
      simp only [d150526, d158218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150526, d158218, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150527 q = 1) (hb : d152855 q = 1) : d158219 q = 1 := by
    cases bit : q 181 with
    | false =>
      simp only [d150527, d158219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150527, d158219, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30713 (p : Pattern) (ha : d150533 p = 1) (hb : d152855 p = 1) : d158225 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150528 q = 1) (hb : d152855 q = 1) : d158220 q = 1 := by
    cases bit : q 177 with
    | false =>
      simp only [d150528, d158220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30712 q ha hb
    | true =>
      simp only [d150528, d158220, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150529 q = 1) (hb : d152855 q = 1) : d158221 q = 1 := by
    cases bit : q 164 with
    | false =>
      simp only [d150529, d158221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150529, d158221, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150530 q = 1) (hb : d152855 q = 1) : d158222 q = 1 := by
    cases bit : q 156 with
    | false =>
      simp only [d150530, d158222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150530, d158222, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150531 q = 1) (hb : d152855 q = 1) : d158223 q = 1 := by
    cases bit : q 155 with
    | false =>
      simp only [d150531, d158223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150531, d158223, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150532 q = 1) (hb : d152855 q = 1) : d158224 q = 1 := by
    cases bit : q 134 with
    | false =>
      simp only [d150532, d158224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150532, d158224, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150533 q = 1) (hb : d152855 q = 1) : d158225 q = 1 := by
    cases bit : q 133 with
    | false =>
      simp only [d150533, d158225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150533, d158225, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30714 (p : Pattern) (ha : d150539 p = 1) (hb : d152855 p = 1) : d158231 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150534 q = 1) (hb : d152855 q = 1) : d158226 q = 1 := by
    cases bit : q 120 with
    | false =>
      simp only [d150534, d158226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30713 q ha hb
    | true =>
      simp only [d150534, d158226, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150535 q = 1) (hb : d152855 q = 1) : d158227 q = 1 := by
    cases bit : q 118 with
    | false =>
      simp only [d150535, d158227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150535, d158227, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150536 q = 1) (hb : d152855 q = 1) : d158228 q = 1 := by
    cases bit : q 114 with
    | false =>
      simp only [d150536, d158228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150536, d158228, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150537 q = 1) (hb : d152855 q = 1) : d158229 q = 1 := by
    cases bit : q 111 with
    | false =>
      simp only [d150537, d158229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150537, d158229, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150538 q = 1) (hb : d152855 q = 1) : d158230 q = 1 := by
    cases bit : q 98 with
    | false =>
      simp only [d150538, d158230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150538, d158230, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150539 q = 1) (hb : d152855 q = 1) : d158231 q = 1 := by
    cases bit : q 97 with
    | false =>
      simp only [d150539, d158231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150539, d158231, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30715 (p : Pattern) (ha : d150545 p = 1) (hb : d152855 p = 1) : d158237 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150540 q = 1) (hb : d152855 q = 1) : d158232 q = 1 := by
    cases bit : q 94 with
    | false =>
      simp only [d150540, d158232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30714 q ha hb
    | true =>
      simp only [d150540, d158232, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150541 q = 1) (hb : d152855 q = 1) : d158233 q = 1 := by
    cases bit : q 76 with
    | false =>
      simp only [d150541, d158233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150541, d158233, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150542 q = 1) (hb : d152855 q = 1) : d158234 q = 1 := by
    cases bit : q 67 with
    | false =>
      simp only [d150542, d158234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150542, d158234, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150543 q = 1) (hb : d152855 q = 1) : d158235 q = 1 := by
    cases bit : q 52 with
    | false =>
      simp only [d150543, d158235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150543, d158235, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150544 q = 1) (hb : d152855 q = 1) : d158236 q = 1 := by
    cases bit : q 47 with
    | false =>
      simp only [d150544, d158236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150544, d158236, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150545 q = 1) (hb : d152855 q = 1) : d158237 q = 1 := by
    cases bit : q 46 with
    | false =>
      simp only [d150545, d158237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150545, d158237, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30716 (p : Pattern) (ha : d150551 p = 1) (hb : d152855 p = 1) : d158243 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d152855 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d150546 q = 1) (hb : d152855 q = 1) : d158238 q = 1 := by
    cases bit : q 45 with
    | false =>
      simp only [d150546, d158238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30715 q ha hb
    | true =>
      simp only [d150546, d158238, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h2 (q : Pattern) (ha : d150547 q = 1) (hb : d152855 q = 1) : d158239 q = 1 := by
    cases bit : q 30 with
    | false =>
      simp only [d150547, d158239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d150547, d158239, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h3 (q : Pattern) (ha : d150548 q = 1) (hb : d152855 q = 1) : d158240 q = 1 := by
    cases bit : q 29 with
    | false =>
      simp only [d150548, d158240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d150548, d158240, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h4 (q : Pattern) (ha : d150549 q = 1) (hb : d152855 q = 1) : d158241 q = 1 := by
    cases bit : q 28 with
    | false =>
      simp only [d150549, d158241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d150549, d158241, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h5 (q : Pattern) (ha : d150550 q = 1) (hb : d152855 q = 1) : d158242 q = 1 := by
    cases bit : q 27 with
    | false =>
      simp only [d150550, d158242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d150550, d158242, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  have h6 (q : Pattern) (ha : d150551 q = 1) (hb : d152855 q = 1) : d158243 q = 1 := by
    cases bit : q 25 with
    | false =>
      simp only [d150551, d158243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d150551, d158243, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q ha hb
  exact h6 p ha hb
theorem andIntro30717 (p : Pattern) (ha : d155083 p = 1) (hb : d156617 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155051 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155057 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d155078 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h5 (q : Pattern) (ha : d155079 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155079, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d155079, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d154974 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d155080 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155080, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155080, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d155081 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155081, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155081, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155082 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155082, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155082, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155083 q = 1) (hb : d156617 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155083, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155083, d156617, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30718 (p : Pattern) (ha : d155099 p = 1) (hb : d156624 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155051 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155057 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155078 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d154973 q = 1) (hb : d156555 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
    | true =>
      simp only [d154973, d156555, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h5 (q : Pattern) (ha : d155079 q = 1) (hb : d156613 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155079, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155079, d156613, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d154974 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d155080 q = 1) (hb : d156614 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155080, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155080, d156614, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d155081 q = 1) (hb : d156615 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155081, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155081, d156615, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155082 q = 1) (hb : d156616 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155082, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155082, d156616, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155088 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d155092 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d0 q = 1) (hb : d155094 q = 1) : d0 q = 1 := by
    exact ha
  have h13 (q : Pattern) (ha : d154980 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
    | true =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
  have h14 (q : Pattern) (ha : d155095 q = 1) (hb : d156620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155095, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q hb ha
    | true =>
      simp only [d155095, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
  have h15 (q : Pattern) (ha : d0 q = 1) (hb : d154981 q = 1) : d0 q = 1 := by
    exact ha
  have h16 (q : Pattern) (ha : d155096 q = 1) (hb : d156621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155096, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d155096, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q hb ha
  have h17 (q : Pattern) (ha : d155097 q = 1) (hb : d156622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155097, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d155097, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155098 q = 1) (hb : d156623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155098, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d155098, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  have h19 (q : Pattern) (ha : d155099 q = 1) (hb : d156624 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155099, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155099, d156624, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30719 (p : Pattern) (ha : d155108 p = 1) (hb : d156818 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155094 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d154980 q = 1) (hb : d156562 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
    | true =>
      simp only [d154980, d156562, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155095 q = 1) (hb : d156620 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155095, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155095, d156620, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d154981 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155096 q = 1) (hb : d156621 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155096, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155096, d156621, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155106 q = 1) (hb : d156622 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155106, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155106, d156622, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155107 q = 1) (hb : d156623 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155107, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155107, d156623, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155108 q = 1) (hb : d156818 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155108, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155108, d156818, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30720 (p : Pattern) (ha : d155137 p = 1) (hb : d156859 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155132 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155014 q = 1) (hb : d156596 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155014, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30401 q ha hb
    | true =>
      simp only [d155014, d156596, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h3 (q : Pattern) (ha : d155133 q = 1) (hb : d156855 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155133, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155133, d156855, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155015 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155134 q = 1) (hb : d156856 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155134, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155134, d156856, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155135 q = 1) (hb : d156857 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155135, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155135, d156857, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155136 q = 1) (hb : d156858 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155136, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155136, d156858, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155137 q = 1) (hb : d156859 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155137, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155137, d156859, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30721 (p : Pattern) (ha : d155143 p = 1) (hb : d158042 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155045 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155100 q = 1) (hb : d156625 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155100, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30717 q ha hb
    | true =>
      simp only [d155100, d156625, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30718 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155102 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155103 q = 1) (hb : d156626 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155103, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155103, d156626, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155104 q = 1) (hb : d158032 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155104, d158032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155104, d158032, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155105 q = 1) (hb : d158033 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155105, d158033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155105, d158033, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155109 q = 1) (hb : d156819 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155109, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155109, d156819, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30719 q ha hb
  have h8 (q : Pattern) (ha : d155110 q = 1) (hb : d158034 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155110, d158034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155110, d158034, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h9 (q : Pattern) (ha : d155111 q = 1) (hb : d158035 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155111, d158035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155111, d158035, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h10 (q : Pattern) (ha : d155112 q = 1) (hb : d158036 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155112, d158036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155112, d158036, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d155113 q = 1) (hb : d158037 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155113, d158037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155113, d158037, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
  have h12 (q : Pattern) (ha : d155138 q = 1) (hb : d156860 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155138, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155138, d156860, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30720 q ha hb
  have h13 (q : Pattern) (ha : d155139 q = 1) (hb : d158038 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155139, d158038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155139, d158038, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h14 (q : Pattern) (ha : d155140 q = 1) (hb : d158039 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155140, d158039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155140, d158039, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h15 (q : Pattern) (ha : d155141 q = 1) (hb : d158040 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155141, d158040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q ha hb
    | true =>
      simp only [d155141, d158040, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h16 (q : Pattern) (ha : d155142 q = 1) (hb : d158041 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155142, d158041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155142, d158041, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d155143 q = 1) (hb : d158042 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155143, d158042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
    | true =>
      simp only [d155143, d158042, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  exact h17 p ha hb
theorem andIntro30722 (p : Pattern) (ha : d155149 p = 1) (hb : d158048 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155030 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155144 q = 1) (hb : d158043 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155144, d158043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155144, d158043, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30721 q ha hb
  have h3 (q : Pattern) (ha : d155145 q = 1) (hb : d158044 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155145, d158044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155145, d158044, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155146 q = 1) (hb : d158045 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155146, d158045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155146, d158045, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155147 q = 1) (hb : d158046 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155147, d158046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155147, d158046, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155148 q = 1) (hb : d158047 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155148, d158047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155148, d158047, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155149 q = 1) (hb : d158048 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155149, d158048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155149, d158048, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  exact h7 p ha hb
theorem andIntro30723 (p : Pattern) (ha : d155215 p = 1) (hb : d156735 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155170 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155176 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d155204 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d155078 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
    | true =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
  have h5 (q : Pattern) (ha : d155205 q = 1) (hb : d156731 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155205, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d155205, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d155211 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d155212 q = 1) (hb : d156732 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155212, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155212, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d155213 q = 1) (hb : d156733 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155213, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155213, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155214 q = 1) (hb : d156734 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155214, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155214, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155215 q = 1) (hb : d156735 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155215, d156735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155215, d156735, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30724 (p : Pattern) (ha : d155234 p = 1) (hb : d156742 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155170 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155176 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155204 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155078 q = 1) (hb : d156659 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30411 q ha hb
    | true =>
      simp only [d155078, d156659, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30394 q ha hb
  have h4 (q : Pattern) (ha : d155205 q = 1) (hb : d156731 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155205, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155205, d156731, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d155211 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d155212 q = 1) (hb : d156732 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155212, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155212, d156732, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d155213 q = 1) (hb : d156733 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155213, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155213, d156733, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155214 q = 1) (hb : d156734 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155214, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155214, d156734, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155220 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155224 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d155226 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d155094 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30415 q ha hb
    | true =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
  have h13 (q : Pattern) (ha : d155227 q = 1) (hb : d156738 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155227, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d155227, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155230 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155231 q = 1) (hb : d156739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155231, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155231, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d155232 q = 1) (hb : d156740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155232, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d155232, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d155233 q = 1) (hb : d156741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155233, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d155233, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155234 q = 1) (hb : d156742 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155234, d156742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155234, d156742, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30725 (p : Pattern) (ha : d155243 p = 1) (hb : d158051 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155226 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155094 q = 1) (hb : d156675 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30415 q ha hb
    | true =>
      simp only [d155094, d156675, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30396 q ha hb
  have h3 (q : Pattern) (ha : d155227 q = 1) (hb : d156738 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155227, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155227, d156738, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155230 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155231 q = 1) (hb : d156739 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155231, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155231, d156739, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155241 q = 1) (hb : d156740 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155241, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155241, d156740, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155242 q = 1) (hb : d156741 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155242, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155242, d156741, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155243 q = 1) (hb : d158051 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155243, d158051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155243, d158051, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30726 (p : Pattern) (ha : d155285 p = 1) (hb : d158061 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155274 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155132 q = 1) (hb : d156713 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155132, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30421 q ha hb
    | true =>
      simp only [d155132, d156713, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30401 q ha hb
  have h3 (q : Pattern) (ha : d155275 q = 1) (hb : d158057 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155275, d158057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155275, d158057, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155281 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155282 q = 1) (hb : d158058 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155282, d158058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155282, d158058, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155283 q = 1) (hb : d158059 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155283, d158059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155283, d158059, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155284 q = 1) (hb : d158060 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155284, d158060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155284, d158060, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155285 q = 1) (hb : d158061 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155285, d158061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155285, d158061, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30727 (p : Pattern) (ha : d155297 p = 1) (hb : d158067 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155164 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155235 q = 1) (hb : d156743 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155235, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30723 q ha hb
    | true =>
      simp only [d155235, d156743, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30724 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155237 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155238 q = 1) (hb : d156744 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155238, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155238, d156744, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155239 q = 1) (hb : d158049 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155239, d158049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155239, d158049, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155240 q = 1) (hb : d158050 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155240, d158050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155240, d158050, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155244 q = 1) (hb : d158052 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155244, d158052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155244, d158052, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30725 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d155246 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d155247 q = 1) (hb : d158053 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155247, d158053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155247, d158053, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d155248 q = 1) (hb : d158054 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155248, d158054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155248, d158054, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d155249 q = 1) (hb : d158055 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155249, d158055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155249, d158055, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d155250 q = 1) (hb : d158056 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155250, d158056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155250, d158056, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155286 q = 1) (hb : d158062 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155286, d158062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155286, d158062, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30726 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155292 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155293 q = 1) (hb : d158063 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155293, d158063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155293, d158063, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d155294 q = 1) (hb : d158064 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155294, d158064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155294, d158064, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d155295 q = 1) (hb : d158065 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155295, d158065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155295, d158065, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d155296 q = 1) (hb : d158066 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155296, d158066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155296, d158066, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d155297 q = 1) (hb : d158067 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155297, d158067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155297, d158067, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30728 (p : Pattern) (ha : d155303 p = 1) (hb : d158073 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155298 q = 1) (hb : d158068 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155298, d158068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155298, d158068, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30727 q ha hb
  have h2 (q : Pattern) (ha : d155299 q = 1) (hb : d158069 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155299, d158069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155299, d158069, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155300 q = 1) (hb : d158070 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155300, d158070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155300, d158070, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155301 q = 1) (hb : d158071 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155301, d158071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155301, d158071, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155302 q = 1) (hb : d158072 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155302, d158072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155302, d158072, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155303 q = 1) (hb : d158073 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155303, d158073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155303, d158073, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30729 (p : Pattern) (ha : d155400 p = 1) (hb : d156904 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155348 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155357 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d155389 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d155322 q = 1) (hb : d156899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30454 q ha hb
    | true =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30455 q ha hb
  have h5 (q : Pattern) (ha : d155390 q = 1) (hb : d156900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155390, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d155390, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d155396 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d155397 q = 1) (hb : d156901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155397, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155397, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d155398 q = 1) (hb : d156902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155398, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155398, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155399 q = 1) (hb : d156903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155399, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155399, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155400 q = 1) (hb : d156904 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155400, d156904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155400, d156904, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30730 (p : Pattern) (ha : d155421 p = 1) (hb : d156914 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155348 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155357 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155389 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155322 q = 1) (hb : d156899 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30454 q ha hb
    | true =>
      simp only [d155322, d156899, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30455 q ha hb
  have h4 (q : Pattern) (ha : d155390 q = 1) (hb : d156900 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155390, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155390, d156900, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d155396 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d155397 q = 1) (hb : d156901 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155397, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155397, d156901, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d155398 q = 1) (hb : d156902 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155398, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155398, d156902, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155399 q = 1) (hb : d156903 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155399, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155399, d156903, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155406 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155411 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d155413 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d155332 q = 1) (hb : d156909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155332, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30457 q ha hb
    | true =>
      simp only [d155332, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30458 q ha hb
  have h13 (q : Pattern) (ha : d155414 q = 1) (hb : d156910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155414, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d155414, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155417 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155418 q = 1) (hb : d156911 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155418, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155418, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d155419 q = 1) (hb : d156912 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155419, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d155419, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d155420 q = 1) (hb : d156913 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155420, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d155420, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155421 q = 1) (hb : d156914 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155421, d156914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155421, d156914, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30731 (p : Pattern) (ha : d155441 p = 1) (hb : d158077 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155413 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155332 q = 1) (hb : d156909 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155332, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30457 q ha hb
    | true =>
      simp only [d155332, d156909, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30458 q ha hb
  have h3 (q : Pattern) (ha : d155414 q = 1) (hb : d156910 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155414, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155414, d156910, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155417 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155418 q = 1) (hb : d156911 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155418, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155418, d156911, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155439 q = 1) (hb : d156912 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155439, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155439, d156912, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155440 q = 1) (hb : d156913 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155440, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155440, d156913, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155441 q = 1) (hb : d158077 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155441, d158077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155441, d158077, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30732 (p : Pattern) (ha : d155505 p = 1) (hb : d158088 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155489 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155494 q = 1) (hb : d158083 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155494, d158083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30490 q ha hb
    | true =>
      simp only [d155494, d158083, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30493 q ha hb
  have h3 (q : Pattern) (ha : d155495 q = 1) (hb : d158084 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155495, d158084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155495, d158084, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155501 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155502 q = 1) (hb : d158085 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155502, d158085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155502, d158085, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155503 q = 1) (hb : d158086 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155503, d158086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155503, d158086, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155504 q = 1) (hb : d158087 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155504, d158087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155504, d158087, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155505 q = 1) (hb : d158088 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155505, d158088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155505, d158088, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30733 (p : Pattern) (ha : d155518 p = 1) (hb : d158094 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155340 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155422 q = 1) (hb : d156915 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155422, d156915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30729 q ha hb
    | true =>
      simp only [d155422, d156915, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30730 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155435 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155436 q = 1) (hb : d156916 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155436, d156916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155436, d156916, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155437 q = 1) (hb : d158075 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155437, d158075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155437, d158075, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155438 q = 1) (hb : d158076 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155438, d158076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155438, d158076, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155442 q = 1) (hb : d158078 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155442, d158078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155442, d158078, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30731 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d155444 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d155445 q = 1) (hb : d158079 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155445, d158079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155445, d158079, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d155446 q = 1) (hb : d158080 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155446, d158080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155446, d158080, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d155447 q = 1) (hb : d158081 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155447, d158081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155447, d158081, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d155448 q = 1) (hb : d158082 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155448, d158082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155448, d158082, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155506 q = 1) (hb : d158089 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155506, d158089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155506, d158089, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30732 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155513 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155514 q = 1) (hb : d158090 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155514, d158090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155514, d158090, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d155515 q = 1) (hb : d158091 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155515, d158091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155515, d158091, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d155516 q = 1) (hb : d158092 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155516, d158092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155516, d158092, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d155517 q = 1) (hb : d158093 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155517, d158093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155517, d158093, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d155518 q = 1) (hb : d158094 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155518, d158094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155518, d158094, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30734 (p : Pattern) (ha : d155524 p = 1) (hb : d158100 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155519 q = 1) (hb : d158095 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155519, d158095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155519, d158095, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30733 q ha hb
  have h2 (q : Pattern) (ha : d155520 q = 1) (hb : d158096 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155520, d158096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155520, d158096, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155521 q = 1) (hb : d158097 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155521, d158097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155521, d158097, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155522 q = 1) (hb : d158098 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155522, d158098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155522, d158098, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155523 q = 1) (hb : d158099 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155523, d158099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155523, d158099, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155524 q = 1) (hb : d158100 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155524, d158100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155524, d158100, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30735 (p : Pattern) (ha : d155675 p = 1) (hb : d157162 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155613 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155622 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d155664 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d155587 q = 1) (hb : d157157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155587, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30507 q ha hb
    | true =>
      simp only [d155587, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30508 q ha hb
  have h5 (q : Pattern) (ha : d155665 q = 1) (hb : d157158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155665, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d155665, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d155671 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d155672 q = 1) (hb : d157159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155672, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155672, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d155673 q = 1) (hb : d157160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155673, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155673, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d155674 q = 1) (hb : d157161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155674, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155674, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d155675 q = 1) (hb : d157162 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155675, d157162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155675, d157162, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30736 (p : Pattern) (ha : d155697 p = 1) (hb : d157172 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155613 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155622 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155664 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155587 q = 1) (hb : d157157 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155587, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30507 q ha hb
    | true =>
      simp only [d155587, d157157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30508 q ha hb
  have h4 (q : Pattern) (ha : d155665 q = 1) (hb : d157158 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155665, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155665, d157158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d155671 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d155672 q = 1) (hb : d157159 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155672, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d155672, d157159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d155673 q = 1) (hb : d157160 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155673, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155673, d157160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155674 q = 1) (hb : d157161 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155674, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155674, d157161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d155681 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d155686 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d155689 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d155597 q = 1) (hb : d157167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155597, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30510 q ha hb
    | true =>
      simp only [d155597, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30511 q ha hb
  have h13 (q : Pattern) (ha : d155690 q = 1) (hb : d157168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155690, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d155690, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155693 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155694 q = 1) (hb : d157169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155694, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155694, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d155695 q = 1) (hb : d157170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155695, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d155695, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d155696 q = 1) (hb : d157171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155696, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d155696, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d155697 q = 1) (hb : d157172 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155697, d157172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d155697, d157172, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30737 (p : Pattern) (ha : d155722 p = 1) (hb : d158105 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155689 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155597 q = 1) (hb : d157167 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155597, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30510 q ha hb
    | true =>
      simp only [d155597, d157167, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30511 q ha hb
  have h3 (q : Pattern) (ha : d155690 q = 1) (hb : d157168 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155690, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155690, d157168, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155693 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155694 q = 1) (hb : d157169 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155694, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155694, d157169, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155720 q = 1) (hb : d157170 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155720, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155720, d157170, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155721 q = 1) (hb : d157171 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155721, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155721, d157171, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155722 q = 1) (hb : d158105 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155722, d158105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155722, d158105, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30738 (p : Pattern) (ha : d155815 p = 1) (hb : d157349 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155810 q = 1) (hb : d157336 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155810, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30550 q ha hb
    | true =>
      simp only [d155810, d157336, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d155811 q = 1) (hb : d157337 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155811, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155811, d157337, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155801 q = 1) (hb : d157344 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d155801, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30548 q ha hb
    | true =>
      simp only [d155801, d157344, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d155802 q = 1) (hb : d157345 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d155802, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155802, d157345, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155812 q = 1) (hb : d157346 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d155812, d157346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d155812, d157346, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155813 q = 1) (hb : d157347 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d155813, d157347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d155813, d157347, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d155814 q = 1) (hb : d157348 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d155814, d157348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155814, d157348, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d155815 q = 1) (hb : d157349 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d155815, d157349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155815, d157349, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30739 (p : Pattern) (ha : d155831 p = 1) (hb : d158116 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155807 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155820 q = 1) (hb : d158111 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155820, d158111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30738 q ha hb
    | true =>
      simp only [d155820, d158111, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30553 q ha hb
  have h3 (q : Pattern) (ha : d155821 q = 1) (hb : d158112 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155821, d158112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d155821, d158112, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d155827 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155828 q = 1) (hb : d158113 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d155828, d158113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155828, d158113, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155829 q = 1) (hb : d158114 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d155829, d158114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155829, d158114, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155830 q = 1) (hb : d158115 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d155830, d158115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155830, d158115, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d155831 q = 1) (hb : d158116 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d155831, d158116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155831, d158116, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30740 (p : Pattern) (ha : d155844 p = 1) (hb : d158122 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155605 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155698 q = 1) (hb : d157173 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155698, d157173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30735 q ha hb
    | true =>
      simp only [d155698, d157173, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30736 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155716 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155717 q = 1) (hb : d157174 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155717, d157174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d155717, d157174, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d155718 q = 1) (hb : d158103 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155718, d158103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d155718, d158103, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d155719 q = 1) (hb : d158104 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155719, d158104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155719, d158104, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d155723 q = 1) (hb : d158106 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155723, d158106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155723, d158106, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30737 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d155725 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d155726 q = 1) (hb : d158107 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155726, d158107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d155726, d158107, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d155727 q = 1) (hb : d158108 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155727, d158108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d155727, d158108, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d155728 q = 1) (hb : d158109 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155728, d158109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d155728, d158109, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d155729 q = 1) (hb : d158110 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155729, d158110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d155729, d158110, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d155832 q = 1) (hb : d158117 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d155832, d158117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d155832, d158117, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30739 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d155839 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d155840 q = 1) (hb : d158118 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d155840, d158118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d155840, d158118, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d155841 q = 1) (hb : d158119 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d155841, d158119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d155841, d158119, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d155842 q = 1) (hb : d158120 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d155842, d158120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d155842, d158120, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d155843 q = 1) (hb : d158121 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d155843, d158121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d155843, d158121, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d155844 q = 1) (hb : d158122 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d155844, d158122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d155844, d158122, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30741 (p : Pattern) (ha : d155850 p = 1) (hb : d158128 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d155845 q = 1) (hb : d158123 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d155845, d158123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155845, d158123, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30740 q ha hb
  have h2 (q : Pattern) (ha : d155846 q = 1) (hb : d158124 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d155846, d158124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155846, d158124, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d155847 q = 1) (hb : d158125 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d155847, d158125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155847, d158125, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d155848 q = 1) (hb : d158126 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d155848, d158126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155848, d158126, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d155849 q = 1) (hb : d158127 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d155849, d158127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155849, d158127, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d155850 q = 1) (hb : d158128 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d155850, d158128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d155850, d158128, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30742 (p : Pattern) (ha : d156008 p = 1) (hb : d157450 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155947 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155956 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d155997 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d155921 q = 1) (hb : d157445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155921, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30567 q ha hb
    | true =>
      simp only [d155921, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30568 q ha hb
  have h5 (q : Pattern) (ha : d155998 q = 1) (hb : d157446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155998, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d155998, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d156004 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156005 q = 1) (hb : d157447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156005, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156005, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d156006 q = 1) (hb : d157448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156006, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d156006, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156007 q = 1) (hb : d157449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156007, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156007, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156008 q = 1) (hb : d157450 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156008, d157450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156008, d157450, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
theorem andIntro30743 (p : Pattern) (ha : d156030 p = 1) (hb : d157460 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155947 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d155956 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d155997 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d155921 q = 1) (hb : d157445 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155921, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30567 q ha hb
    | true =>
      simp only [d155921, d157445, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30568 q ha hb
  have h4 (q : Pattern) (ha : d155998 q = 1) (hb : d157446 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d155998, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d155998, d157446, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d0 q = 1) (hb : d156004 q = 1) : d0 q = 1 := by
    exact ha
  have h6 (q : Pattern) (ha : d156005 q = 1) (hb : d157447 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156005, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
    | true =>
      simp only [d156005, d157447, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q hb ha
  have h7 (q : Pattern) (ha : d156006 q = 1) (hb : d157448 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156006, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156006, d157448, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156007 q = 1) (hb : d157449 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156007, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156007, d157449, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d0 q = 1) (hb : d156014 q = 1) : d0 q = 1 := by
    exact ha
  have h10 (q : Pattern) (ha : d0 q = 1) (hb : d156019 q = 1) : d0 q = 1 := by
    exact ha
  have h11 (q : Pattern) (ha : d0 q = 1) (hb : d156022 q = 1) : d0 q = 1 := by
    exact ha
  have h12 (q : Pattern) (ha : d155931 q = 1) (hb : d157455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155931, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30570 q ha hb
    | true =>
      simp only [d155931, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30571 q ha hb
  have h13 (q : Pattern) (ha : d156023 q = 1) (hb : d157456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156023, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q hb ha
    | true =>
      simp only [d156023, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d156026 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156027 q = 1) (hb : d157457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156027, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156027, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d156028 q = 1) (hb : d157458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156028, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q hb ha
    | true =>
      simp only [d156028, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
  have h17 (q : Pattern) (ha : d156029 q = 1) (hb : d157459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156029, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q hb ha
    | true =>
      simp only [d156029, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
  have h18 (q : Pattern) (ha : d156030 q = 1) (hb : d157460 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156030, d157460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
    | true =>
      simp only [d156030, d157460, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
  exact h18 p ha hb
theorem andIntro30744 (p : Pattern) (ha : d156055 p = 1) (hb : d158134 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156022 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d155931 q = 1) (hb : d157455 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d155931, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30570 q ha hb
    | true =>
      simp only [d155931, d157455, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30571 q ha hb
  have h3 (q : Pattern) (ha : d156023 q = 1) (hb : d157456 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156023, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156023, d157456, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156026 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156027 q = 1) (hb : d157457 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156027, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156027, d157457, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156053 q = 1) (hb : d157458 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156053, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156053, d157458, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156054 q = 1) (hb : d157459 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156054, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156054, d157459, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156055 q = 1) (hb : d158134 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156055, d158134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156055, d158134, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30745 (p : Pattern) (ha : d156152 p = 1) (hb : d158143 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156147 q = 1) (hb : d157667 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156147, d157667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30610 q ha hb
    | true =>
      simp only [d156147, d157667, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h2 (q : Pattern) (ha : d156148 q = 1) (hb : d157668 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156148, d157668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156148, d157668, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156138 q = 1) (hb : d157657 q = 1) : d0 q = 1 := by
    cases bit : q 116 with
    | false =>
      simp only [d156138, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30608 q ha hb
    | true =>
      simp only [d156138, d157657, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h4 (q : Pattern) (ha : d156139 q = 1) (hb : d157658 q = 1) : d0 q = 1 := by
    cases bit : q 115 with
    | false =>
      simp only [d156139, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156139, d157658, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156149 q = 1) (hb : d158140 q = 1) : d0 q = 1 := by
    cases bit : q 113 with
    | false =>
      simp only [d156149, d158140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
    | true =>
      simp only [d156149, d158140, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156150 q = 1) (hb : d158141 q = 1) : d0 q = 1 := by
    cases bit : q 96 with
    | false =>
      simp only [d156150, d158141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156150, d158141, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h7 (q : Pattern) (ha : d156151 q = 1) (hb : d158142 q = 1) : d0 q = 1 := by
    cases bit : q 95 with
    | false =>
      simp only [d156151, d158142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156151, d158142, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  have h8 (q : Pattern) (ha : d156152 q = 1) (hb : d158143 q = 1) : d0 q = 1 := by
    cases bit : q 93 with
    | false =>
      simp only [d156152, d158143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156152, d158143, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
  exact h8 p ha hb
theorem andIntro30746 (p : Pattern) (ha : d156168 p = 1) (hb : d158149 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156144 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d156157 q = 1) (hb : d158144 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156157, d158144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30745 q ha hb
    | true =>
      simp only [d156157, d158144, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30613 q ha hb
  have h3 (q : Pattern) (ha : d156158 q = 1) (hb : d158145 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156158, d158145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156158, d158145, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d156164 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156165 q = 1) (hb : d158146 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156165, d158146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156165, d158146, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156166 q = 1) (hb : d158147 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156166, d158147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156166, d158147, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156167 q = 1) (hb : d158148 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156167, d158148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156167, d158148, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
  have h8 (q : Pattern) (ha : d156168 q = 1) (hb : d158149 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156168, d158149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156168, d158149, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  exact h8 p ha hb
theorem andIntro30747 (p : Pattern) (ha : d156181 p = 1) (hb : d158155 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d155939 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156031 q = 1) (hb : d157461 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156031, d157461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30742 q ha hb
    | true =>
      simp only [d156031, d157461, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30743 q ha hb
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156049 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d156050 q = 1) (hb : d157462 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156050, d157462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
    | true =>
      simp only [d156050, d157462, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
  have h4 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h5 (q : Pattern) (ha : d156051 q = 1) (hb : d158132 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156051, d158132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
    | true =>
      simp only [d156051, d158132, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h6 (q : Pattern) (ha : d156052 q = 1) (hb : d158133 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156052, d158133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156052, d158133, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  have h7 (q : Pattern) (ha : d156056 q = 1) (hb : d158135 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156056, d158135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d156056, d158135, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30744 q ha hb
  have h8 (q : Pattern) (ha : d0 q = 1) (hb : d156058 q = 1) : d0 q = 1 := by
    exact ha
  have h9 (q : Pattern) (ha : d156059 q = 1) (hb : d158136 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156059, d158136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
    | true =>
      simp only [d156059, d158136, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q hb ha
  have h10 (q : Pattern) (ha : d156060 q = 1) (hb : d158137 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156060, d158137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
    | true =>
      simp only [d156060, d158137, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h11 (q : Pattern) (ha : d156061 q = 1) (hb : d158138 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156061, d158138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h10 q ha hb
    | true =>
      simp only [d156061, d158138, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h12 (q : Pattern) (ha : d156062 q = 1) (hb : d158139 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156062, d158139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q ha hb
    | true =>
      simp only [d156062, d158139, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h11 q ha hb
  have h13 (q : Pattern) (ha : d156169 q = 1) (hb : d158150 q = 1) : d0 q = 1 := by
    cases bit : q 70 with
    | false =>
      simp only [d156169, d158150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
    | true =>
      simp only [d156169, d158150, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30746 q ha hb
  have h14 (q : Pattern) (ha : d0 q = 1) (hb : d156176 q = 1) : d0 q = 1 := by
    exact ha
  have h15 (q : Pattern) (ha : d156177 q = 1) (hb : d158151 q = 1) : d0 q = 1 := by
    cases bit : q 69 with
    | false =>
      simp only [d156177, d158151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h13 q ha hb
    | true =>
      simp only [d156177, d158151, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h14 q hb ha
  have h16 (q : Pattern) (ha : d156178 q = 1) (hb : d158152 q = 1) : d0 q = 1 := by
    cases bit : q 51 with
    | false =>
      simp only [d156178, d158152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h15 q ha hb
    | true =>
      simp only [d156178, d158152, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h17 (q : Pattern) (ha : d156179 q = 1) (hb : d158153 q = 1) : d0 q = 1 := by
    cases bit : q 50 with
    | false =>
      simp only [d156179, d158153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h16 q ha hb
    | true =>
      simp only [d156179, d158153, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h18 (q : Pattern) (ha : d156180 q = 1) (hb : d158154 q = 1) : d0 q = 1 := by
    cases bit : q 49 with
    | false =>
      simp only [d156180, d158154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h17 q ha hb
    | true =>
      simp only [d156180, d158154, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q hb ha
  have h19 (q : Pattern) (ha : d156181 q = 1) (hb : d158155 q = 1) : d0 q = 1 := by
    cases bit : q 48 with
    | false =>
      simp only [d156181, d158155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h12 q ha hb
    | true =>
      simp only [d156181, d158155, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h18 q ha hb
  exact h19 p ha hb
theorem andIntro30748 (p : Pattern) (ha : d156187 p = 1) (hb : d158161 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d156182 q = 1) (hb : d158156 q = 1) : d0 q = 1 := by
    cases bit : q 10260 with
    | false =>
      simp only [d156182, d158156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156182, d158156, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30747 q ha hb
  have h2 (q : Pattern) (ha : d156183 q = 1) (hb : d158157 q = 1) : d0 q = 1 := by
    cases bit : q 10259 with
    | false =>
      simp only [d156183, d158157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156183, d158157, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q ha hb
  have h3 (q : Pattern) (ha : d156184 q = 1) (hb : d158158 q = 1) : d0 q = 1 := by
    cases bit : q 10258 with
    | false =>
      simp only [d156184, d158158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156184, d158158, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q ha hb
  have h4 (q : Pattern) (ha : d156185 q = 1) (hb : d158159 q = 1) : d0 q = 1 := by
    cases bit : q 10257 with
    | false =>
      simp only [d156185, d158159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156185, d158159, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q ha hb
  have h5 (q : Pattern) (ha : d156186 q = 1) (hb : d158160 q = 1) : d0 q = 1 := by
    cases bit : q 10256 with
    | false =>
      simp only [d156186, d158160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156186, d158160, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d156187 q = 1) (hb : d158161 q = 1) : d0 q = 1 := by
    cases bit : q 10255 with
    | false =>
      simp only [d156187, d158161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156187, d158161, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
  exact h6 p ha hb
theorem andIntro30749 (p : Pattern) (ha : d156324 p = 1) (hb : d157763 p = 1) : d0 p = 1 := by
  have h0 (q : Pattern) (ha : d0 q = 1) (hb : d1 q = 1) : d0 q = 1 := by
    exact ha
  have h1 (q : Pattern) (ha : d0 q = 1) (hb : d156277 q = 1) : d0 q = 1 := by
    exact ha
  have h2 (q : Pattern) (ha : d0 q = 1) (hb : d156286 q = 1) : d0 q = 1 := by
    exact ha
  have h3 (q : Pattern) (ha : d0 q = 1) (hb : d156313 q = 1) : d0 q = 1 := by
    exact ha
  have h4 (q : Pattern) (ha : d156251 q = 1) (hb : d157758 q = 1) : d0 q = 1 := by
    cases bit : q 91 with
    | false =>
      simp only [d156251, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30627 q ha hb
    | true =>
      simp only [d156251, d157758, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact andIntro30628 q ha hb
  have h5 (q : Pattern) (ha : d156314 q = 1) (hb : d157759 q = 1) : d0 q = 1 := by
    cases bit : q 90 with
    | false =>
      simp only [d156314, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h3 q hb ha
    | true =>
      simp only [d156314, d157759, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h4 q ha hb
  have h6 (q : Pattern) (ha : d0 q = 1) (hb : d156320 q = 1) : d0 q = 1 := by
    exact ha
  have h7 (q : Pattern) (ha : d156321 q = 1) (hb : d157760 q = 1) : d0 q = 1 := by
    cases bit : q 89 with
    | false =>
      simp only [d156321, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h5 q ha hb
    | true =>
      simp only [d156321, d157760, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h6 q hb ha
  have h8 (q : Pattern) (ha : d156322 q = 1) (hb : d157761 q = 1) : d0 q = 1 := by
    cases bit : q 74 with
    | false =>
      simp only [d156322, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h2 q hb ha
    | true =>
      simp only [d156322, d157761, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h7 q ha hb
  have h9 (q : Pattern) (ha : d156323 q = 1) (hb : d157762 q = 1) : d0 q = 1 := by
    cases bit : q 73 with
    | false =>
      simp only [d156323, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h1 q hb ha
    | true =>
      simp only [d156323, d157762, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h8 q ha hb
  have h10 (q : Pattern) (ha : d156324 q = 1) (hb : d157763 q = 1) : d0 q = 1 := by
    cases bit : q 71 with
    | false =>
      simp only [d156324, d157763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h0 q hb ha
    | true =>
      simp only [d156324, d157763, bit, Bool.false_eq_true, ↓reduceIte] at ha hb ⊢
      all_goals
        exact h9 q ha hb
  exact h10 p ha hb
end NetHack.Soko22Hazard87
